import Langlands.Representation.Archimedean.RealCartanArgumentDifferential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Determinant

/-! # Lower coordinates for the Cartan argument differential -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealCartanLowerCoordinates

open RealCartanPeakTest RealCartanArgumentDifferential RealLeviChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "L" n:max => (LowerIndex n → ℝ)

section Split

variable {c : ℕ} (sz : Fin c → ℕ)
local notation "N" => ∑ i, sz i

/-- The lower matrix entries inside individual Levi blocks. -/
abbrev WithinIndex := {pq : LowerIndex N // ¬ cls sz pq.1.2 < cls sz pq.1.1}

theorem cls_eq_of_withinIndex (p : WithinIndex sz) : cls sz p.1.1.2 = cls sz p.1.1.1 :=
  (cls_mono sz p.1.2.le).antisymm (le_of_not_gt p.2)

private def offDiagonalIndexEquiv :
    Coord sz ≃ {pq : LowerIndex N // cls sz pq.1.2 < cls sz pq.1.1} where
  toFun p := ⟨⟨p.1, lt_of_cls_lt sz p.2⟩, p.2⟩
  invFun p := ⟨p.1.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The off-block and within-block positions partition the strictly lower entries. -/
def lowerIndexEquiv : Coord sz ⊕ WithinIndex sz ≃ LowerIndex N :=
  (Equiv.sumCongr (offDiagonalIndexEquiv sz) (Equiv.refl _)).trans (Equiv.sumCompl _)

theorem lowerIndexEquiv_inl (p : Coord sz) :
    lowerIndexEquiv sz (Sum.inl p) = ⟨p.1, lt_of_cls_lt sz p.2⟩ := rfl

theorem lowerIndexEquiv_inr (p : WithinIndex sz) : lowerIndexEquiv sz (Sum.inr p) = p.1 := rfl

/-- Join the two families of lower coordinates, preserving product Lebesgue measure. -/
def joinLower : ((Coord sz → ℝ) × (WithinIndex sz → ℝ)) ≃L[ℝ] L N :=
  ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Coord sz) (WithinIndex sz) fun _ => ℝ).symm).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) (lowerIndexEquiv sz))

@[simp]
theorem joinLower_apply_off (X : Coord sz → ℝ) (Z : WithinIndex sz → ℝ) (p : Coord sz) :
    joinLower sz (X, Z) (lowerIndexEquiv sz (.inl p)) = X p := by
  simp [joinLower, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]
  rfl

@[simp]
theorem joinLower_apply_within (X : Coord sz → ℝ) (Z : WithinIndex sz → ℝ)
    (p : WithinIndex sz) : joinLower sz (X, Z) (lowerIndexEquiv sz (.inr p)) = Z p := by
  simp [joinLower, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]
  rfl

theorem measurePreserving_joinLower : MeasurePreserving (joinLower sz) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (lowerIndexEquiv sz)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm fun _ : Coord sz ⊕ WithinIndex sz => ℝ)

end Split

section Skew

variable {n : ℕ}

private def skewMatrix (X : L n) : M n :=
  Matrix.of fun p q => if h : q < p then X ⟨(p, q), h⟩
    else if h : p < q then -X ⟨(q, p), h⟩ else 0

/-- Fill a real skew-symmetric matrix from its strictly lower coordinates. -/
def skewLower (n : ℕ) : L n →L[ℝ] M n :=
  ({ toFun := skewMatrix
     map_add' := fun X Y => by
       ext p q
       simp only [skewMatrix, Matrix.of_apply, Matrix.add_apply]
       split_ifs <;> simp [add_comm]
     map_smul' := fun t X => by
       ext p q
       simp only [skewMatrix, Matrix.of_apply, Matrix.smul_apply]
       split_ifs <;> simp
   } : L n →ₗ[ℝ] M n).toContinuousLinearMap

theorem skewLower_apply (X : L n) (p q : Fin n) :
    skewLower n X p q = if h : q < p then X ⟨(p, q), h⟩
      else if h : p < q then -X ⟨(q, p), h⟩ else 0 := rfl

theorem transpose_skewLower (X : L n) : (skewLower n X)ᵀ = -(skewLower n X) := by
  ext p q
  change skewLower n X q p = -(skewLower n X p q)
  rcases lt_trichotomy p q with h | rfl | h
  · simp [skewLower_apply, h, not_lt_of_gt h]
  · simp [skewLower_apply]
  · simp [skewLower_apply, h, not_lt_of_gt h]

@[simp]
theorem lowerProjection_skewLower (X : L n) : lowerProjection n (skewLower n X) = X := by
  funext p
  rw [lowerProjection_apply, skewLower_apply, dite_eq_left p.2]

theorem skewLower_lowerProjection {A : M n} (hA : Aᵀ = -A) :
    skewLower n (lowerProjection n A) = A := by
  have he (p q : Fin n) : A q p = -A p q := congrArg (fun Z : M n => Z p q) hA
  ext p q
  rw [skewLower_apply]
  rcases lt_trichotomy p q with h | rfl | h
  · rw [dite_eq_right (not_lt_of_gt h), dite_eq_left h, lowerProjection_apply, he, neg_neg]
  · simp only [lt_irrefl, ↓reduceDIte]
    linarith [he p p]
  · rw [dite_eq_left h, lowerProjection_apply]

theorem conjugation_transpose_eq_neg (W A : M n) (hA : Aᵀ = -A) :
    (conjugationCLM W A)ᵀ = -(conjugationCLM W A) := by
  simp only [conjugationCLM_apply, transpose_mul, transpose_transpose, hA,
    Matrix.mul_neg, Matrix.neg_mul, mul_assoc]

/-- Orthogonal conjugation on skew matrices in strictly lower coordinates. -/
def projectedConjugation (W : K n) : L n →L[ℝ] L n :=
  (lowerProjection n).comp ((conjugationCLM (W : M n)).comp (skewLower n))

theorem projectedConjugation_apply (W : K n) (X : L n) :
    projectedConjugation W X = lowerProjection n (conjugationCLM (W : M n) (skewLower n X)) := rfl

@[simp]
theorem projectedConjugation_one : projectedConjugation (1 : K n) = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro X
  simp [projectedConjugation_apply]

theorem projectedConjugation_mul (W V : K n) :
    projectedConjugation (W * V) = (projectedConjugation W).comp (projectedConjugation V) := by
  apply ContinuousLinearMap.ext
  intro X
  simp only [ContinuousLinearMap.comp_apply, projectedConjugation_apply]
  rw [skewLower_lowerProjection (conjugation_transpose_eq_neg _ _ (transpose_skewLower X))]
  simp only [Submonoid.coe_mul, conjugationCLM_apply, transpose_mul, mul_assoc]

/-- The inverse is conjugation by the inverse orthogonal matrix. -/
def projectedConjugationEquiv (W : K n) : L n ≃L[ℝ] L n :=
  ContinuousLinearEquiv.equivOfInverse' (projectedConjugation W)
    (projectedConjugation W⁻¹)
    (by rw [← projectedConjugation_mul, mul_inv_cancel, projectedConjugation_one])
    (by rw [← projectedConjugation_mul, inv_mul_cancel, projectedConjugation_one])

private def projectedConjugationDet (n : ℕ) : K n →* ℝ where
  toFun W := (projectedConjugation W).det
  map_one' := by rw [projectedConjugation_one]; exact LinearMap.det_id
  map_mul' W V := by rw [projectedConjugation_mul]; exact LinearMap.det_comp _ _

private theorem continuous_projectedConjugationDet (n : ℕ) : Continuous (projectedConjugationDet n) := by
  let b := Pi.basisFun ℝ (LowerIndex n)
  change Continuous (fun W : K n => LinearMap.det (projectedConjugation W).toLinearMap)
  simp only [← LinearMap.det_toMatrix b]
  apply Continuous.matrix_det
  apply continuous_matrix
  intro p q
  simp only [LinearMap.toMatrix_apply, b, Pi.basisFun_repr, ContinuousLinearMap.coe_coe,
    projectedConjugation_apply, conjugationCLM_apply, lowerProjection_apply]
  exact ((continuous_subtype_val.matrix_mul continuous_const).matrix_mul
    continuous_subtype_val.matrix_transpose).matrix_elem _ _

/-- The absolute determinant of the orthogonal transport in lower coordinates is one. -/
theorem abs_det_projectedConjugation (W : K n) : |(projectedConjugation W).det| = 1 := by
  have hK : CompactSpace (K n) := isCompact_iff_compactSpace.mp
    (RealPrincipalSeriesDuality.isCompact_unitaryGroup_set n)
  let D := projectedConjugationDet n
  have hc : Continuous D := continuous_projectedConjugationDet n
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (univ : Set (K n))).exists_bound_of_continuousOn
    hc.continuousOn
  have hle (u : K n) : ‖D u‖ ≤ 1 := by
    by_contra hn
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (lt_of_not_ge hn)
    have hb := hC (u ^ m) (mem_univ _)
    rw [map_pow, norm_pow] at hb
    exact (not_lt_of_ge hb) hm
  have hm : ‖D W‖ * ‖D W⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  have hlow : 1 ≤ ‖D W‖ := calc
    1 = ‖D W‖ * ‖D W⁻¹‖ := hm.symm
    _ ≤ ‖D W‖ * 1 := mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)
    _ = ‖D W‖ := mul_one _
  exact le_antisymm (hle W) hlow

end Skew

/-- Lower coordinates identify the joint transverse spaces with the flat
Lebesgue coordinates, and the orthogonal conjugation is volume preserving. -/
def RealCartanLowerCoordinatesStatement : Prop :=
  (∀ (c : ℕ) (sz : Fin c → ℕ), MeasurePreserving (joinLower sz) volume volume) ∧
    ∀ (n : ℕ) (W : K n), |(projectedConjugation W).det| = 1

theorem realCartanLowerCoordinates : RealCartanLowerCoordinatesStatement :=
  ⟨fun _ _ => measurePreserving_joinLower _, fun _ _ => abs_det_projectedConjugation _⟩

end Langlands.Archimedean.RealCartanLowerCoordinates
