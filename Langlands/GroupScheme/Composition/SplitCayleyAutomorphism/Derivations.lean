import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.RootGroups
import Langlands.GroupScheme.GeneralLinearDualNumber

/-! # Derivations of Zorn's split Cayley algebra -/

noncomputable section

universe u

open Langlands.GroupScheme.GeneralLinear.DualNumber Matrix

namespace Langlands.GroupScheme

namespace SplitCayley

section Ring

variable {A : Type u} [CommRing A]

/-- The linear part `X_α` of the root-group element `x_α(r) = 1 + r X_α + r² X_α⁽²⁾`. -/
def rootDerFun : Root → (Fin 8 → A) → (Fin 8 → A)
  | .u1, x => ![-x 4, x 0 - x 7, 0, 0, 0, -x 3, x 2, x 4]
  | .u2, x => ![-x 5, 0, x 0 - x 7, 0, x 3, 0, -x 1, x 5]
  | .u3, x => ![-x 6, 0, 0, x 0 - x 7, -x 2, x 1, 0, x 6]
  | .v1, x => ![-x 1, 0, -x 6, x 5, x 0 - x 7, 0, 0, x 1]
  | .v2, x => ![-x 2, x 6, 0, -x 4, 0, x 0 - x 7, 0, x 2]
  | .v3, x => ![-x 3, -x 5, x 4, 0, 0, 0, x 0 - x 7, x 3]
  | .l12, x => ![0, x 2, 0, 0, 0, -x 4, 0, 0]
  | .l13, x => ![0, x 3, 0, 0, 0, 0, -x 4, 0]
  | .l21, x => ![0, 0, x 1, 0, -x 5, 0, 0, 0]
  | .l23, x => ![0, 0, x 3, 0, 0, 0, -x 5, 0]
  | .l31, x => ![0, 0, 0, x 1, -x 6, 0, 0, 0]
  | .l32, x => ![0, 0, 0, x 2, 0, -x 6, 0, 0]

/-- The quadratic part `X_α⁽²⁾` of the root-group element `x_α(r)`. -/
def rootSqFun : Root → (Fin 8 → A) → (Fin 8 → A)
  | .u1, x => ![0, -x 4, 0, 0, 0, 0, 0, 0]
  | .u2, x => ![0, 0, -x 5, 0, 0, 0, 0, 0]
  | .u3, x => ![0, 0, 0, -x 6, 0, 0, 0, 0]
  | .v1, x => ![0, 0, 0, 0, -x 1, 0, 0, 0]
  | .v2, x => ![0, 0, 0, 0, 0, -x 2, 0, 0]
  | .v3, x => ![0, 0, 0, 0, 0, 0, -x 3, 0]
  | .l12, _ => 0
  | .l13, _ => 0
  | .l21, _ => 0
  | .l23, _ => 0
  | .l31, _ => 0
  | .l32, _ => 0

theorem rootFun_eq (α : Root) (r : A) (x : Fin 8 → A) :
    rootFun α r x = x + r • rootDerFun α x + r ^ 2 • rootSqFun α x := by
  cases α <;> funext i <;> fin_cases i <;> simp only [rootFun, rootDerFun,
    rootSqFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.cons_val,
    Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

/-- The derivative `diag(0, a, b, -a-b, -a, -b, a+b, 0)` of the torus at the identity. -/
def torusDerFun (a b : A) (x : Fin 8 → A) : Fin 8 → A :=
  ![0, a * x 1, b * x 2, -(a + b) * x 3, -a * x 4, -b * x 5, (a + b) * x 6, 0]

/-- A function on `A⁸` is a derivation of Zorn's product. -/
def IsDerivation (f : (Fin 8 → A) → (Fin 8 → A)) : Prop :=
  ∀ x y, f (mulFun A x y) = mulFun A (f x) y + mulFun A x (f y)

theorem rootDerFun_add (α : Root) (x y : Fin 8 → A) :
    rootDerFun α (x + y) = rootDerFun α x + rootDerFun α y := by
  cases α <;> funext i <;> fin_cases i <;> simp [rootDerFun] <;> ring

theorem rootDerFun_smul (α : Root) (c : A) (x : Fin 8 → A) :
    rootDerFun α (c • x) = c • rootDerFun α x := by
  cases α <;> funext i <;> fin_cases i <;> simp [rootDerFun] <;> ring

theorem torusDerFun_add (a b : A) (x y : Fin 8 → A) :
    torusDerFun a b (x + y) = torusDerFun a b x + torusDerFun a b y := by
  funext i; fin_cases i <;> simp [torusDerFun] <;> ring

theorem torusDerFun_smul (a b c : A) (x : Fin 8 → A) :
    torusDerFun a b (c • x) = c • torusDerFun a b x := by
  funext i; fin_cases i <;> simp [torusDerFun] <;> ring

theorem isDerivation_torusDerFun (a b : A) : IsDerivation (torusDerFun a b) := by
  intro x y
  funext i
  fin_cases i <;> simp only [torusDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_u1 : IsDerivation (rootDerFun (A := A) .u1) := by
  intro x y
  funext i
  fin_cases i <;> simp [rootDerFun, mulFun] <;> ring

theorem isDerivation_rootDerFun_u2 : IsDerivation (rootDerFun (A := A) .u2) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_u3 : IsDerivation (rootDerFun (A := A) .u3) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_v1 : IsDerivation (rootDerFun (A := A) .v1) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_v2 : IsDerivation (rootDerFun (A := A) .v2) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_v3 : IsDerivation (rootDerFun (A := A) .v3) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_l12 : IsDerivation (rootDerFun (A := A) .l12) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_l13 : IsDerivation (rootDerFun (A := A) .l13) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_l21 : IsDerivation (rootDerFun (A := A) .l21) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_l23 : IsDerivation (rootDerFun (A := A) .l23) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_l31 : IsDerivation (rootDerFun (A := A) .l31) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun_l32 : IsDerivation (rootDerFun (A := A) .l32) := by
  intro x y
  funext i
  fin_cases i <;> simp only [rootDerFun, mulFun, Matrix.cons_val, Fin.isValue, Pi.add_apply,
    Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem isDerivation_rootDerFun (α : Root) : IsDerivation (rootDerFun (A := A) α) := by
  cases α
  · exact isDerivation_rootDerFun_u1
  · exact isDerivation_rootDerFun_u2
  · exact isDerivation_rootDerFun_u3
  · exact isDerivation_rootDerFun_v1
  · exact isDerivation_rootDerFun_v2
  · exact isDerivation_rootDerFun_v3
  · exact isDerivation_rootDerFun_l12
  · exact isDerivation_rootDerFun_l13
  · exact isDerivation_rootDerFun_l21
  · exact isDerivation_rootDerFun_l23
  · exact isDerivation_rootDerFun_l31
  · exact isDerivation_rootDerFun_l32

/-! ### Matrices of the root and torus derivations -/

/-- The root derivation `X_α` as an `A`-linear map. -/
def rootDerLin (α : Root) : (Fin 8 → A) →ₗ[A] (Fin 8 → A) where
  toFun := rootDerFun α
  map_add' := rootDerFun_add α
  map_smul' := rootDerFun_smul α

/-- The matrix of the root derivation `X_α`. -/
def rootDer (α : Root) : Matrix (Fin 8) (Fin 8) A :=
  LinearMap.toMatrix' (rootDerLin α)

theorem rootDer_mulVec (α : Root) (x : Fin 8 → A) : rootDer α *ᵥ x = rootDerFun α x :=
  LinearMap.toMatrix'_mulVec (rootDerLin α) x

theorem rootDer_apply (α : Root) (i j : Fin 8) :
    rootDer (A := A) α i j = rootDerFun α (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply (rootDerLin α) i j

/-- The diagonal derivation `diag(0, a, b, -a-b, -a, -b, a+b, 0)` of the torus. -/
def torusDer (a b : A) : Matrix (Fin 8) (Fin 8) A :=
  Matrix.diagonal ![0, a, b, -(a + b), -a, -b, a + b, 0]

theorem torusDer_mulVec (a b : A) (x : Fin 8 → A) : torusDer a b *ᵥ x = torusDerFun a b x := by
  funext i
  rw [torusDer, Matrix.mulVec_diagonal]
  fin_cases i <;> simp [torusDerFun]

theorem torusDer_apply (a b : A) (i j : Fin 8) :
    torusDer a b i j = if i = j then ![0, a, b, -(a + b), -a, -b, a + b, 0] i else 0 := by
  rw [torusDer, Matrix.diagonal_apply]

theorem torusDer_add (a b a' b' : A) :
    torusDer (a + a') (b + b') = torusDer a b + torusDer a' b' := by
  rw [torusDer, torusDer, torusDer, Matrix.diagonal_add]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem torusDer_smul (c a b : A) : torusDer (c * a) (c * b) = c • torusDer a b := by
  rw [torusDer, torusDer, ← Matrix.diagonal_smul]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

theorem torusDer_eq (a b : A) : torusDer a b = a • torusDer 1 0 + b • torusDer 0 1 := by
  rw [← torusDer_smul, ← torusDer_smul, ← torusDer_add]
  congr 1 <;> ring

/-- The combination `Σ_α D_{p(α)} X_α + H(D₁₁, D₂₂)` of root and torus derivations, with the
pivot entry `p(α)` of each root derivation. -/
def derivCombination (D : Matrix (Fin 8) (Fin 8) A) : Matrix (Fin 8) (Fin 8) A :=
  D 1 0 • rootDer .u1 + D 2 0 • rootDer .u2 + D 3 0 • rootDer .u3 + D 3 5 • rootDer .v1 +
    D 1 6 • rootDer .v2 + D 2 4 • rootDer .v3 + D 1 2 • rootDer .l12 + D 1 3 • rootDer .l13 +
    D 2 1 • rootDer .l21 + D 2 3 • rootDer .l23 + D 3 1 • rootDer .l31 +
    D 3 2 • rootDer .l32 + torusDer (D 1 1) (D 2 2)

/-- The Leibniz rule of a derivation matrix on pairs of standard basis vectors. -/
theorem leibniz_single {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec)
    (j k i : Fin 8) :
    (D *ᵥ mulFun A (Pi.single j 1) (Pi.single k 1)) i =
      mulFun A (fun l => D l j) (Pi.single k 1) i +
        mulFun A (Pi.single j 1) (fun l => D l k) i := by
  have h := congrFun (hD (Pi.single j 1) (Pi.single k 1)) i
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact h

/-- Normalization of entries of the Leibniz identities and of `derivCombination`. -/
local macro "deriv_norm" : tactic =>
  `(tactic| (simp (config := { decide := true }) only [derivCombination, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, rootDer_apply, torusDer_apply, rootDerFun, mulFun,
      Matrix.mulVec, dotProduct, Fin.sum_univ_eight, Pi.single_apply, Matrix.cons_val,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ↓reduceIte, mul_one,
      mul_zero, zero_mul, one_mul, Pi.zero_apply]; ring1))

theorem derivCombination_row0 {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) (j : Fin 8) :
    D 0 j = derivCombination D 0 j := by
  have h := leibniz_single hD
  fin_cases j
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 0 0
  · linear_combination (norm := deriv_norm) (-1 : A) * h 1 3 3
  · linear_combination (norm := deriv_norm) (-1 : A) * h 2 1 1
  · linear_combination (norm := deriv_norm) (-1 : A) * h 3 2 2
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 4 0
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 5 0
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 6 0
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 7 0

theorem derivCombination_row1 {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) (j : Fin 8) :
    D 1 j = derivCombination D 1 j := by
  have h := leibniz_single hD
  fin_cases j
  · deriv_norm
  · deriv_norm
  · deriv_norm
  · deriv_norm
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 4 1
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 4 2 + (-1 : A) * h 0 5 1
  · deriv_norm
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 7 1

theorem derivCombination_row2 {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) (j : Fin 8) :
    D 2 j = derivCombination D 2 j := by
  have h := leibniz_single hD
  fin_cases j
  · deriv_norm
  · deriv_norm
  · deriv_norm
  · deriv_norm
  · deriv_norm
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 5 2
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 5 3 + (-1 : A) * h 0 6 2
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 7 2

theorem derivCombination_row3 {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) (j : Fin 8) :
    D 3 j = derivCombination D 3 j := by
  have h := leibniz_single hD
  fin_cases j
  · deriv_norm
  · deriv_norm
  · deriv_norm
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 0 0 + (-1 : A) * h 1 4 0 + (-1 : A) * h 2 3 4
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 4 3 + (-1 : A) * h 0 6 1
  · deriv_norm
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 6 3
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 7 3

theorem derivCombination_row4 {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) (j : Fin 8) :
    D 4 j = derivCombination D 4 j := by
  have h := leibniz_single hD
  fin_cases j
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 5 3
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 1 4
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 2 4
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 3 4
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 0 0 + (-1 : A) * h 1 4 0
  · linear_combination (norm := deriv_norm) (-1 : A) * h 1 3 4
  · linear_combination (norm := deriv_norm) (1 : A) * h 1 2 4
  · linear_combination (norm := deriv_norm) (1 : A) * h 5 2 4

theorem derivCombination_row5 {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) (j : Fin 8) :
    D 5 j = derivCombination D 5 j := by
  have h := leibniz_single hD
  fin_cases j
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 6 1
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 1 5
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 2 5
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 3 5
  · linear_combination (norm := deriv_norm) (1 : A) * h 2 3 5
  · linear_combination (norm := deriv_norm) (-1 : A) * h 0 0 0 + (-1 : A) * h 1 3 5 + (-1 : A) * h 1 4 0 + (-1 : A) * h 2 3 4
  · linear_combination (norm := deriv_norm) (1 : A) * h 1 2 5
  · linear_combination (norm := deriv_norm) (1 : A) * h 6 3 5

theorem derivCombination_row6 {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) (j : Fin 8) :
    D 6 j = derivCombination D 6 j := by
  have h := leibniz_single hD
  fin_cases j
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 4 2
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 1 6
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 2 6
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 3 6
  · linear_combination (norm := deriv_norm) (1 : A) * h 2 3 6
  · linear_combination (norm := deriv_norm) (-1 : A) * h 1 3 6
  · linear_combination (norm := deriv_norm) (1 : A) * h 1 2 6
  · linear_combination (norm := deriv_norm) (1 : A) * h 4 1 6

theorem derivCombination_row7 {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) (j : Fin 8) :
    D 7 j = derivCombination D 7 j := by
  have h := leibniz_single hD
  fin_cases j
  · linear_combination (norm := deriv_norm) (1 : A) * h 0 0 7
  · linear_combination (norm := deriv_norm) (-1 : A) * h 1 5 5
  · linear_combination (norm := deriv_norm) (-1 : A) * h 1 2 1
  · linear_combination (norm := deriv_norm) (-1 : A) * h 2 3 2
  · linear_combination (norm := deriv_norm) (-1 : A) * h 1 4 1
  · linear_combination (norm := deriv_norm) (-1 : A) * h 2 5 2
  · linear_combination (norm := deriv_norm) (-1 : A) * h 3 6 3
  · linear_combination (norm := deriv_norm) (-1 : A) * h 1 7 1


/-- Every derivation matrix of Zorn's algebra is the explicit combination of the twelve root
derivations and the torus derivation. -/
theorem eq_derivCombination {D : Matrix (Fin 8) (Fin 8) A} (hD : IsDerivation D.mulVec) :
    D = derivCombination D := by
  ext i j
  fin_cases i
  · exact derivCombination_row0 hD j
  · exact derivCombination_row1 hD j
  · exact derivCombination_row2 hD j
  · exact derivCombination_row3 hD j
  · exact derivCombination_row4 hD j
  · exact derivCombination_row5 hD j
  · exact derivCombination_row6 hD j
  · exact derivCombination_row7 hD j

theorem mulFun_add_left (x x' y : Fin 8 → A) :
    mulFun A (x + x') y = mulFun A x y + mulFun A x' y := by
  change mul A (x + x') y = mul A x y + mul A x' y
  rw [map_add, LinearMap.add_apply]

theorem mulFun_add_right (x y y' : Fin 8 → A) :
    mulFun A x (y + y') = mulFun A x y + mulFun A x y' :=
  map_add (mul A x) y y'

/-! ### Dual numbers -/

section DualNumber

open TrivSqZeroExt

/-- The vector of first components of a dual-number vector. -/
def fstVec (z : Fin 8 → DualNumber A) : Fin 8 → A := fun i => (z i).fst

/-- The vector of `ε`-components of a dual-number vector. -/
def sndVec (z : Fin 8 → DualNumber A) : Fin 8 → A := fun i => (z i).snd

/-- The constant dual-number vector of a vector. -/
def inlVec (x : Fin 8 → A) : Fin 8 → DualNumber A := fun i => inl (x i)

@[simp] theorem fstVec_inlVec (x : Fin 8 → A) : fstVec (inlVec x) = x := rfl

@[simp] theorem sndVec_inlVec (x : Fin 8 → A) : sndVec (inlVec x) = 0 := by
  funext i
  simp [sndVec, inlVec]

omit [CommRing A] in
theorem vec_ext {z w : Fin 8 → DualNumber A} (h1 : fstVec z = fstVec w)
    (h2 : sndVec z = sndVec w) : z = w := by
  funext i
  exact TrivSqZeroExt.ext (congrFun h1 i) (congrFun h2 i)

theorem fstVec_mulFun (z w : Fin 8 → DualNumber A) :
    fstVec (mulFun (DualNumber A) z w) = mulFun A (fstVec z) (fstVec w) := by
  funext i
  fin_cases i <;> simp [mulFun, fstVec]

theorem sndVec_mulFun (z w : Fin 8 → DualNumber A) :
    sndVec (mulFun (DualNumber A) z w) =
      mulFun A (fstVec z) (sndVec w) + mulFun A (sndVec z) (fstVec w) := by
  funext i
  fin_cases i <;> simp [mulFun, fstVec, sndVec] <;> ring

theorem fstVec_unit : fstVec (unit (DualNumber A)) = unit A := by
  funext i
  fin_cases i <;> simp [fstVec, unit]

theorem sndVec_unit : sndVec (unit (DualNumber A)) = 0 := by
  funext i
  fin_cases i <;> simp [sndVec, unit]

theorem fstVec_one_add_epsilonMatrix_mulVec (D : Matrix (Fin 8) (Fin 8) A)
    (z : Fin 8 → DualNumber A) : fstVec ((1 + epsilonMatrix D) *ᵥ z) = fstVec z := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  funext i
  simp [fstVec, Matrix.mulVec, dotProduct, TrivSqZeroExt.fst_sum]

theorem sndVec_one_add_epsilonMatrix_mulVec (D : Matrix (Fin 8) (Fin 8) A)
    (z : Fin 8 → DualNumber A) :
    sndVec ((1 + epsilonMatrix D) *ᵥ z) = sndVec z + D *ᵥ fstVec z := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  funext i
  simp [sndVec, fstVec, Matrix.mulVec, dotProduct, TrivSqZeroExt.snd_sum, mul_comm]

/-- `1 + εD` is an automorphism of Zorn's algebra over the dual numbers exactly when `D` kills
the unit and is a derivation. -/
theorem isAutomorphism_one_add_epsilonMatrix_iff (D : Matrix (Fin 8) (Fin 8) A) :
    IsAutomorphism (fun z => (1 + epsilonMatrix D) *ᵥ z) ↔
      D *ᵥ unit A = 0 ∧ IsDerivation (fun x => D *ᵥ x) := by
  constructor
  · rintro ⟨hu, hm⟩
    refine ⟨?_, fun x y => ?_⟩
    · have h := congrArg sndVec hu
      rw [sndVec_one_add_epsilonMatrix_mulVec, sndVec_unit, fstVec_unit, zero_add] at h
      exact h
    · have h := congrArg sndVec (hm (inlVec x) (inlVec y))
      rw [sndVec_one_add_epsilonMatrix_mulVec, sndVec_mulFun, sndVec_mulFun, fstVec_mulFun,
        fstVec_one_add_epsilonMatrix_mulVec, fstVec_one_add_epsilonMatrix_mulVec,
        sndVec_one_add_epsilonMatrix_mulVec, sndVec_one_add_epsilonMatrix_mulVec] at h
      simp only [fstVec_inlVec, sndVec_inlVec, zero_add] at h
      have h0 : ∀ v : Fin 8 → A, mulFun A v 0 = 0 := fun v => map_zero (mul A v)
      have h0' : ∀ v : Fin 8 → A, mulFun A 0 v = 0 := fun v => by
        change mul A 0 v = 0
        rw [map_zero, LinearMap.zero_apply]
      rw [h0, h0', zero_add, zero_add] at h
      change D *ᵥ mulFun A x y = mulFun A (D *ᵥ x) y + mulFun A x (D *ᵥ y)
      rw [h, add_comm]
  · rintro ⟨hu, hm⟩
    refine ⟨?_, fun z w => ?_⟩
    · apply vec_ext
      · rw [fstVec_one_add_epsilonMatrix_mulVec]
      · rw [sndVec_one_add_epsilonMatrix_mulVec, fstVec_unit, hu, add_zero]
    · apply vec_ext
      · rw [fstVec_one_add_epsilonMatrix_mulVec, fstVec_mulFun, fstVec_mulFun,
          fstVec_one_add_epsilonMatrix_mulVec, fstVec_one_add_epsilonMatrix_mulVec]
      · rw [sndVec_one_add_epsilonMatrix_mulVec, sndVec_mulFun, sndVec_mulFun, fstVec_mulFun,
          fstVec_one_add_epsilonMatrix_mulVec, fstVec_one_add_epsilonMatrix_mulVec,
          sndVec_one_add_epsilonMatrix_mulVec, sndVec_one_add_epsilonMatrix_mulVec,
          mulFun_add_left, mulFun_add_right]
        have h := hm (fstVec z) (fstVec w)
        simp only at h
        rw [h]
        abel

end DualNumber

end Ring

end SplitCayley

end Langlands.GroupScheme
