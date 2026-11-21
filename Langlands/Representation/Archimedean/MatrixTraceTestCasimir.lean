import Langlands.Representation.Archimedean.MatrixTestFunctions
import Langlands.Representation.Archimedean.MatrixTranslationDerivatives

/-! # The trace Casimir on actual compact smooth matrix tests -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Distributions Matrix.Norms.Operator

namespace Langlands.Archimedean

universe uF

variable {F : Type uF} [RCLike F] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "D" => 𝓓(matrixUnitsOpen F n, ℂ)

/-- The real trace Casimir on compactly supported smooth tests on the units. -/
def matrixTraceTestCasimir (F : Type uF) [RCLike F] (n : ℕ) :
    𝓓(matrixUnitsOpen F n, ℂ) →L[ℂ] 𝓓(matrixUnitsOpen F n, ℂ) :=
  ∑ i, (matrixLeftTestDerivative (matrixTraceUnit F n i)).comp
    (matrixLeftTestDerivative (matrixTraceDualUnit F n i))

@[simp]
theorem matrixTraceTestCasimir_apply (f : D) (x : M) :
    matrixTraceTestCasimir F n f x = matrixTraceCasimir (f : M → ℂ) x := by
  change (∑ i, (matrixLeftTestDerivative (matrixTraceUnit F n i)).comp
    (matrixLeftTestDerivative (matrixTraceDualUnit F n i))) f x = _
  simp only [sum_apply, ContinuousLinearMap.comp_apply, matrixTraceCasimir]
  rfl

theorem matrixLeftTestDerivative_add (X Y : M) (f : D) :
    matrixLeftTestDerivative (X + Y) f = matrixLeftTestDerivative X f + matrixLeftTestDerivative Y f := by
  ext x
  change fderiv ℝ (f : M → ℂ) x ((X + Y) * x) =
    fderiv ℝ (f : M → ℂ) x (X * x) + fderiv ℝ (f : M → ℂ) x (Y * x)
  rw [add_mul, map_add]

theorem matrixLeftTestDerivative_real_smul (r : ℝ) (X : M) (f : D) :
    matrixLeftTestDerivative (r • X) f = r • matrixLeftTestDerivative X f := by
  ext x
  change fderiv ℝ (f : M → ℂ) x ((r • X) * x) = r • fderiv ℝ (f : M → ℂ) x (X * x)
  rw [smul_mul_assoc, map_smul]

@[simp]
theorem matrixLeftTestDerivative_neg (X : M) (f : D) :
    matrixLeftTestDerivative (-X) f = -matrixLeftTestDerivative X f := by
  ext x
  change fderiv ℝ (f : M → ℂ) x ((-X) * x) = -fderiv ℝ (f : M → ℂ) x (X * x)
  rw [neg_mul, map_neg]

/-- The test-function commutator is the field of the reversed matrix commutator. -/
theorem matrixLeftTestDerivative_commutator (X Y : M) (f : D) :
    matrixLeftTestDerivative X (matrixLeftTestDerivative Y f) -
      matrixLeftTestDerivative Y (matrixLeftTestDerivative X f) =
    matrixLeftTestDerivative (Y * X - X * Y) f := by
  ext x
  exact congrFun (matrixLeftDerivative_commutator f.contDiff X Y) x

/-- The positive roots of the upper triangular subgroup, given by their matrix indices. -/
abbrev MatrixPositiveRoot (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private def matrixIndexEquiv (n : ℕ) :
    (Fin n ⊕ (MatrixPositiveRoot n × Bool)) ≃ (Fin n × Fin n) where
  toFun
    | .inl i => (i, i)
    | .inr (p, false) => p.val
    | .inr (p, true) => (p.val.2, p.val.1)
  invFun p :=
    if h : p.1 = p.2 then .inl p.1
    else if hlt : p.1 < p.2 then .inr (⟨p, hlt⟩, false)
    else .inr (⟨(p.2, p.1), lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)⟩, true)
  left_inv s := by
    cases s with
    | inl i => simp
    | inr q =>
        rcases q with ⟨p, b⟩
        cases b
        · simp [ne_of_lt p.property, p.property]
        · simp [ne_of_gt p.property, not_lt_of_gt p.property]
  right_inv p := by
    rcases p with ⟨i, j⟩
    by_cases h : i = j
    · subst j
      simp
    · by_cases hlt : i < j
      · simp [h, hlt]
      · simp [h, hlt]

private theorem sum_matrix_indices {A : Type*} [AddCommMonoid A] (h : Fin n × Fin n → A) :
    (∑ p, h p) = (∑ i : Fin n, h (i, i)) +
      ∑ p : MatrixPositiveRoot n, (h p.val + h (p.val.2, p.val.1)) := by
  rw [← Equiv.sum_comp (matrixIndexEquiv n) h]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, matrixIndexEquiv, add_comm]

/-- The off-diagonal trace Casimir terms can be reordered so that each
upper-root derivative is applied last. The commutator contributes a
first-order diagonal field. -/
theorem matrixTraceTestCasimir_positive_roots (f : D) :
    matrixTraceTestCasimir F n f =
      (∑ i : Fin n, ∑ k : Bool, matrixLeftTestDerivative (matrixTraceUnit F n (i, i, k))
        (matrixLeftTestDerivative (matrixTraceDualUnit F n (i, i, k)) f)) +
      ∑ p : MatrixPositiveRoot n, ∑ k : Bool,
        let b := matrixTraceUnit F n (p.val.1, p.val.2, k)
        let d := matrixTraceDualUnit F n (p.val.1, p.val.2, k)
        (2 : ℕ) • matrixLeftTestDerivative b (matrixLeftTestDerivative d f) +
          matrixLeftTestDerivative (b * d - d * b) f := by
  let P (i j : Fin n) (k : Bool) :=
    matrixLeftTestDerivative (matrixTraceUnit F n (i, j, k))
      (matrixLeftTestDerivative (matrixTraceDualUnit F n (i, j, k)) f)
  let H (q : Fin n × Fin n) := ∑ k : Bool, P q.1 q.2 k
  have hC : matrixTraceTestCasimir F n f = ∑ q, H q := by
    simp only [matrixTraceTestCasimir, sum_apply, ContinuousLinearMap.comp_apply,
      Fintype.sum_prod_type, H, P]
  rw [hC, sum_matrix_indices]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  change (∑ k : Bool, P p.val.1 p.val.2 k) + (∑ k : Bool, P p.val.2 p.val.1 k) = _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  let b := matrixTraceUnit F n (p.val.1, p.val.2, k)
  let d := matrixTraceDualUnit F n (p.val.1, p.val.2, k)
  have hp : P p.val.2 p.val.1 k = matrixLeftTestDerivative d (matrixLeftTestDerivative b f) := by
    cases k <;> simp [P, b, d, matrixTraceUnit, matrixTraceDualUnit, ← Matrix.single_neg]
  change matrixLeftTestDerivative b (matrixLeftTestDerivative d f) + P p.val.2 p.val.1 k =
    (2 : ℕ) • matrixLeftTestDerivative b (matrixLeftTestDerivative d f) +
      matrixLeftTestDerivative (b * d - d * b) f
  rw [hp]
  let A := matrixLeftTestDerivative b (matrixLeftTestDerivative d f)
  let B := matrixLeftTestDerivative d (matrixLeftTestDerivative b f)
  let C := matrixLeftTestDerivative (b * d - d * b) f
  change A + B = (2 : ℕ) • A + C
  have h : B - A = C := matrixLeftTestDerivative_commutator d b f
  calc
    A + B = A + ((B - A) + A) := by rw [sub_add_cancel]
    _ = _ := by rw [h, two_nsmul]; abel

end Langlands.Archimedean
