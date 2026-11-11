/-!
Quantum computing proofs, core Lean 4 only (no Mathlib, no imports).

Amplitudes are integers. Normalising factors like 1/√2 are kept out of the
statements by scaling: the Hadamard is the unnormalised H' = [[1,1],[1,-1]],
so H'·H' = 2·I, and "probability 1" becomes "amplitude² = 4 out of norm² 4".

1. X·X = I
2. H'·H' = 2·I
3. H'·X·H' = 2·Z
4. H' scales squared norm by exactly 2
5. No-cloning (linear maps cannot clone)
6. Deutsch's algorithm
-/

namespace QC

/-- 2×2 integer matrix. -/
structure M where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq

def M.mul (p q : M) : M :=
  ⟨p.a*q.a + p.b*q.c, p.a*q.b + p.b*q.d,
   p.c*q.a + p.d*q.c, p.c*q.b + p.d*q.d⟩

instance : Mul M := ⟨M.mul⟩

def I2 : M := ⟨1, 0, 0, 1⟩
def X  : M := ⟨0, 1, 1, 0⟩
def Z  : M := ⟨1, 0, 0, -1⟩
def H  : M := ⟨1, 1, 1, -1⟩            -- unnormalised Hadamard
def smul (k : Int) (p : M) : M := ⟨k*p.a, k*p.b, k*p.c, k*p.d⟩

/-! ## 1 (easy) -/
theorem X_mul_X : X * X = I2 := by decide

/-! ## 2 -/
theorem H_mul_H : H * H = smul 2 I2 := by decide

/-! ## 3 -/
theorem H_X_H : H * X * H = smul 2 Z := by decide

/-! ## 4: H' scales the squared norm by 2 (for every integer vector) -/
theorem H_norm (x y : Int) :
    (x + y) * (x + y) + (x - y) * (x - y) = 2 * (x * x + y * y) := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_comm y x]
  omega

/-! ## 5: no-cloning
A "cloner" sends (x,y) to 4 coordinates, is additive, and on every input
equals the tensor square v⊗v = (x·x, x·y, y·x, y·y). -/

structure Cloner where
  T : Int × Int → Int × Int × Int × Int
  add : ∀ u v : Int × Int,
    T (u.1 + v.1, u.2 + v.2) =
      ((T u).1 + (T v).1, (T u).2.1 + (T v).2.1,
       (T u).2.2.1 + (T v).2.2.1, (T u).2.2.2 + (T v).2.2.2)
  clone : ∀ v : Int × Int, T v = (v.1 * v.1, v.1 * v.2, v.2 * v.1, v.2 * v.2)

theorem no_cloning (C : Cloner) : False := by
  have h := C.add (1, 0) (0, 1)
  have h1 := C.clone (1, 0)
  have h2 := C.clone (0, 1)
  have h3 := C.clone (1, 1)
  simp only [Int.add_zero, Int.zero_add] at h
  rw [h3, h1, h2] at h
  simp at h

/-! ## 6: Deutsch's algorithm
Phase oracle on |+⟩ gives amplitudes (σ f0, σ f1) (times 1/√2), σ b = (-1)^b.
Final unnormalised H' puts σ f0 + σ f1 on |0⟩ (norm² of the whole state is 4). -/

def sgn (b : Bool) : Int := if b then -1 else 1
def amp0 (f0 f1 : Bool) : Int := sgn f0 + sgn f1

/-- constant f: all the weight (4 of 4) is on |0⟩ -/
theorem deutsch_constant (f0 f1 : Bool) (h : f0 = f1) :
    amp0 f0 f1 * amp0 f0 f1 = 4 := by
  subst h; cases f0 <;> decide

/-- balanced f: no weight at all on |0⟩ -/
theorem deutsch_balanced (f0 f1 : Bool) (h : f0 ≠ f1) :
    amp0 f0 f1 = 0 := by
  cases f0 <;> cases f1 <;> first | decide | exact absurd rfl h

end QC
