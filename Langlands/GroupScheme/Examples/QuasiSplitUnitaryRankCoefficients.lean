import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul

noncomputable section
universe u v w

namespace Langlands.GroupScheme.QuasiSplitUnitary
namespace RankCoefficients

variable (E : Type u) [CommRing E] (M : Type v) [AddCommMonoid M]

/-- Send an exponent `m` to the diagonal exponent `(m,m)`. -/
def diagonalMap : AddMonoidAlgebra E M →ₐ[E] AddMonoidAlgebra E (M × M) :=
  AddMonoidAlgebra.mapDomainAlgHom E E
    { toFun := fun m => (m, m)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Put all exponents in the first factor. -/
def leftMap : AddMonoidAlgebra E M →ₐ[E] AddMonoidAlgebra E (M × M) :=
  AddMonoidAlgebra.mapDomainAlgHom E E
    { toFun := fun m => (m, 0)
      map_zero' := rfl
      map_add' := fun _ _ => by simp }

/-- Put all exponents in the second factor. -/
def rightMap : AddMonoidAlgebra E M →ₐ[E] AddMonoidAlgebra E (M × M) :=
  AddMonoidAlgebra.mapDomainAlgHom E E
    { toFun := fun m => (0, m)
      map_zero' := rfl
      map_add' := fun _ _ => by simp }

variable {E M}

@[simp] theorem diagonalMap_single (m : M) (r : E) :
    diagonalMap E M (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single (m, m) r := by
  simp [diagonalMap]

@[simp] theorem leftMap_single (m : M) (r : E) :
    leftMap E M (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single (m, 0) r := by
  simp [leftMap]

@[simp] theorem rightMap_single (m : M) (r : E) :
    rightMap E M (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single (0, m) r := by
  simp [rightMap]

variable [DecidableEq M]

/-- A diagonal exponent map contributes only at equal exponents. -/
theorem coeff_diagonalMap (p : AddMonoidAlgebra E M) (a b : M) :
    (diagonalMap E M p).coeff (a, b) = if a = b then p.coeff a else 0 := by
  change Finsupp.mapDomain (fun m : M => (m, m)) p.coeff (a, b) = _
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    exact Finsupp.mapDomain_apply_of_injective
      (fun _ _ h => congrArg Prod.fst h) _ a
  · rw [ite_eq_right hab]
    have hn (m : M) : (m, m) ≠ (a, b) := by
      intro h
      exact hab ((congrArg Prod.fst h).symm.trans (congrArg Prod.snd h))
    simp [Finsupp.mapDomain_apply, hn]

/-- Exponents from the two separate factors multiply without convolution collisions. -/
theorem coeff_leftMap_mul_rightMap (p q : AddMonoidAlgebra E M) (a b : M) :
    (leftMap E M p * rightMap E M q).coeff (a, b) = p.coeff a * q.coeff b := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ h₁ h₂ =>
    simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂]
  | single m r =>
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add q₁ q₂ h₁ h₂ =>
      simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h₁, h₂]
    | single n s =>
      by_cases hma : m = a <;> by_cases hnb : n = b <;>
        simp [AddMonoidAlgebra.single_mul_single,
          Prod.mk.injEq, hma, hnb]

/-- The coefficient matrix of a matrix of Laurent polynomials. -/
def matrixCoeff {n : Type w} (P : Matrix n n (AddMonoidAlgebra E M)) (m : M) : Matrix n n E :=
  fun i j => (P i j).coeff m

/-- Multiplicativity over independent torus variables makes coefficient matrices orthogonal
idempotents. -/
theorem matrixCoeff_mul {n : Type w} [Fintype n]
    (P : Matrix n n (AddMonoidAlgebra E M))
    (hP : P.map (diagonalMap E M) = P.map (leftMap E M) * P.map (rightMap E M))
    (a b : M) :
    matrixCoeff P a * matrixCoeff P b = if a = b then matrixCoeff P a else 0 := by
  ext i j
  have h := congrArg (fun Q : Matrix n n (AddMonoidAlgebra E (M × M)) =>
    (Q i j).coeff (a, b)) hP
  simp only [Matrix.map_apply, Matrix.mul_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, coeff_diagonalMap, coeff_leftMap_mul_rightMap] at h
  by_cases hab : a = b
  · simpa [matrixCoeff, hab, Matrix.mul_apply] using h.symm
  · simpa [matrixCoeff, hab, Matrix.mul_apply] using h.symm

section Negation

variable {K : Type*} [Zero K] {N : Type*} [AddGroup N] {n : Type*}

/-- A coefficient symmetry under exponent negation preserves the zero coefficient matrices. -/
theorem neg_eq_zero_iff (C : N → Matrix n n K) (c : K → K) (hc : c 0 = 0)
    (s : n → n) (hC : ∀ m i j, C (-m) i j = c (C m (s j) (s i))) (m : N) :
    C (-m) = 0 ↔ C m = 0 := by
  have hz (q : N) (hq : C q = 0) : C (-q) = 0 := by
    ext i j
    rw [hC, hq]
    exact hc
  constructor
  · intro h
    simpa using hz (-m) h
  · exact hz m

/-- The nonzero coefficient matrices of such a family are stable under negation. -/
theorem neg_ne_zero_iff (C : N → Matrix n n K) (c : K → K) (hc : c 0 = 0)
    (s : n → n) (hC : ∀ m i j, C (-m) i j = c (C m (s j) (s i))) (m : N) :
    C (-m) ≠ 0 ↔ C m ≠ 0 :=
  not_congr (neg_eq_zero_iff C c hc s hC m)

end Negation

end RankCoefficients
end Langlands.GroupScheme.QuasiSplitUnitary
