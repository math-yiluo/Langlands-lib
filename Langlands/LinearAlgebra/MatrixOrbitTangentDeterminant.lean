import Langlands.LinearAlgebra.MatrixConjugationConormal

/-! # Absolute determinants on real matrix orbit tangents -/

noncomputable section

open Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

private theorem abs_det_eq_one_of_bilin_multiplier {E : Type*} [AddCommGroup E]
    [Module ℝ E] [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E)
    (hB : B.Nondegenerate) (L : E →ₗ[ℝ] E) {c : ℝ} (hc : |c| = 1)
    (h : ∀ x y, B (L x) (L y) = c * B x y) : |LinearMap.det L| = 1 := by
  let D := B.toDual hB
  have he : (D.symm.conj L.dualMap).comp L = c • LinearMap.id := by
    ext1 x
    apply D.injective
    ext y
    change D (D.symm (L.dualMap (D (L x)))) y = D (c • x) y
    rw [D.apply_symm_apply, map_smul]
    exact h x y
  have hd := congrArg LinearMap.det he
  change LinearMap.det ((D.symm.toLinearMap ∘ₗ L.dualMap ∘ₗ D.symm.symm.toLinearMap).comp L) = _ at hd
  rw [LinearMap.det_comp, LinearMap.det_conj L.dualMap D.symm, LinearMap.det_dualMap,
    LinearMap.det_smul, LinearMap.det_id, mul_one] at hd
  apply (abs_pow_eq_one _ (by decide : (2 : ℕ) ≠ 0)).mp
  simpa only [sq, abs_pow, hc, one_pow] using congrArg abs hd

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation:max "T[" A "]" => LinearMap.range (matrixConjugationTangent A)

/-- Conjugation by a unit as a linear equivalence of square matrices. -/
def matrixConjugationLinearEquiv (u : Matˣ) : Mat ≃ₗ[ℝ] Mat :=
  (u.mulLeftLinearEquiv ℝ Mat).trans (u⁻¹.mulRightLinearEquiv ℝ)

@[simp]
theorem matrixConjugationLinearEquiv_apply (u : Matˣ) (X : Mat) :
    matrixConjugationLinearEquiv u X = u.val * X * u.inv := rfl

@[simp]
theorem matrixConjugationLinearEquiv_symm (u : Matˣ) :
    (matrixConjugationLinearEquiv u).symm = matrixConjugationLinearEquiv u⁻¹ := by
  ext1 X
  change u.inv * (X * u.val) = u.inv * X * u.val
  rw [mul_assoc]

/-- Conjugation by the inverse of a unit after matrix transpose. -/
def matrixAdjustedTransposeLinearEquiv (q : Matˣ) : Mat ≃ₗ[ℝ] Mat :=
  (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).trans (matrixConjugationLinearEquiv q⁻¹)

@[simp]
theorem matrixAdjustedTransposeLinearEquiv_apply (q : Matˣ) (X : Mat) :
    matrixAdjustedTransposeLinearEquiv q X = q.inv * Xᵀ * q.val := rfl

private theorem traceBilin_eq_zero_of_mem_conjugationTangent_of_mem_ker
    {A X Y : Mat} (hX : X ∈ T[A]) (hY : Y ∈ LinearMap.ker (matrixConjugationTangent A)) :
    matrixTraceBilin X Y = 0 := by
  have hy : Commute Y A := sub_eq_zero.mp (LinearMap.mem_ker.mp hY)
  exact (mem_matrixTraceBilin_orthogonal_conjugationTangent_iff A Y).mpr hy.symm X hX

/-- The orbit tangent carries the form `B(ad_A X, ad_A Y) = tr((ad_A X) * Y)`.
A right inverse of `ad_A` on its range supplies a representative of the second input. -/
def matrixOrbitTangentForm (A : Mat) (J : T[A] →ₗ[ℝ] Mat) : LinearMap.BilinForm ℝ (T[A]) :=
  matrixTraceBilin.comp (T[A]).subtype J

theorem matrixOrbitTangentForm_nondegenerate (A : Mat) (J : T[A] →ₗ[ℝ] Mat)
    (hJ : ∀ t : T[A], matrixConjugationTangent A (J t) = t) :
    (matrixOrbitTangentForm A J).Nondegenerate := by
  let D := matrixConjugationTangent A
  constructor
  · intro t ht
    apply Subtype.ext
    change t.val = 0
    apply matrixTraceBilin_nondegenerate.1
    intro X
    let s := D.rangeRestrict X
    have hK : X - J s ∈ LinearMap.ker D := by
      apply LinearMap.mem_ker.mpr
      rw [map_sub, hJ]
      exact sub_self (D X)
    have hz := traceBilin_eq_zero_of_mem_conjugationTangent_of_mem_ker t.property hK
    rw [map_sub, sub_eq_zero] at hz
    exact hz.trans (ht s)
  · intro t ht
    have horth : J t ∈ matrixTraceBilin.orthogonal (T[A]) :=
      LinearMap.BilinForm.mem_orthogonal_iff.mpr fun X hX => ht ⟨X, hX⟩
    have hcomm := (mem_matrixTraceBilin_orthogonal_conjugationTangent_iff A (J t)).mp horth
    apply Subtype.ext
    change t.val = 0
    rw [← hJ, matrixConjugationTangent_apply, hcomm.eq, sub_self]

/-- A linear map intertwining the commutator up to a scalar of absolute value one preserves
the orbit tangent. -/
theorem matrixOrbitTangent_invariant_of_intertwines (A : Mat) (L : Mat →ₗ[ℝ] Mat)
    {c : ℝ} (hc : |c| = 1)
    (h : ∀ X, matrixConjugationTangent A (L X) = c • L (matrixConjugationTangent A X)) :
    T[A] ≤ (T[A]).comap L := by
  have hc₂ : c * c = 1 := by rw [← abs_mul_abs_self, hc, mul_one]
  rintro _ ⟨X, rfl⟩
  exact ⟨c • L X, by rw [map_smul, h, smul_smul, hc₂, one_smul]⟩

/-- The restricted action preserves the tangent form up to the same scalar, so its absolute
Jacobian on the orbit tangent is one. -/
theorem abs_det_restrict_matrixOrbitTangent_of_intertwines (A : Mat) (L : Mat →ₗ[ℝ] Mat)
    {c : ℝ} (hc : |c| = 1)
    (hB : ∀ X Y, matrixTraceBilin (L X) (L Y) = matrixTraceBilin X Y)
    (h : ∀ X, matrixConjugationTangent A (L X) = c • L (matrixConjugationTangent A X))
    (hT : T[A] ≤ (T[A]).comap L) :
    |LinearMap.det (L.restrict (p := T[A]) (q := T[A]) hT)| = 1 := by
  let D := matrixConjugationTangent A
  obtain ⟨J, hJ'⟩ := D.rangeRestrict.exists_rightInverse_of_surjective D.range_rangeRestrict
  have hJ (t : T[A]) : D (J t) = t :=
    congrArg Subtype.val (LinearMap.congr_fun hJ' t)
  let R := L.restrict (p := T[A]) (q := T[A]) hT
  apply abs_det_eq_one_of_bilin_multiplier (matrixOrbitTangentForm A J)
    (matrixOrbitTangentForm_nondegenerate A J hJ) R hc
  intro s t
  have hc₂ : c * c = 1 := by rw [← abs_mul_abs_self, hc, mul_one]
  have hK : J (R t) - c • L (J t) ∈ LinearMap.ker D := by
    apply LinearMap.mem_ker.mpr
    rw [map_sub, hJ, map_smul, h, smul_smul, hc₂, one_smul, hJ]
    exact sub_self (L t)
  have hzero := traceBilin_eq_zero_of_mem_conjugationTangent_of_mem_ker (R s).property hK
  rw [map_sub, sub_eq_zero] at hzero
  change matrixTraceBilin (L s) (J (R t)) = matrixTraceBilin (L s) (c • L (J t)) at hzero
  change matrixTraceBilin (L s) (J (R t)) = c * matrixTraceBilin s (J t)
  rw [hzero, map_smul, smul_eq_mul, hB]

theorem matrixConjugationTangent_conjugation {A : Mat} {u : Matˣ}
    (hu : Commute (u : Mat) A) (X : Mat) :
    matrixConjugationTangent A (matrixConjugationLinearEquiv u X) =
      matrixConjugationLinearEquiv u (matrixConjugationTangent A X) := by
  let L := matrixConjugationLinearEquiv u
  have hA : L A = A := by
    rw [matrixConjugationLinearEquiv_apply, hu.eq, mul_assoc, u.val_inv, mul_one]
  have hm (Y Z : Mat) : L (Y * Z) = L Y * L Z := by
    simp [L, mul_assoc]
  change matrixConjugationTangent A (L X) = L (matrixConjugationTangent A X)
  rw [matrixConjugationTangent_apply, matrixConjugationTangent_apply, map_sub, hm, hm, hA]

theorem matrixConjugationTangent_adjustedTranspose {A : Mat} {q : Matˣ}
    (hq : q.val * A * q.inv = Aᵀ) (X : Mat) :
    matrixConjugationTangent A (matrixAdjustedTransposeLinearEquiv q X) =
      -matrixAdjustedTransposeLinearEquiv q (matrixConjugationTangent A X) := by
  let L := matrixAdjustedTransposeLinearEquiv q
  have hA : L A = A := by
    change q.inv * Aᵀ * q.val = A
    rw [← hq]
    simp [mul_assoc]
  have hm (Y Z : Mat) : L (Y * Z) = L Z * L Y := by
    simp [L, transpose_mul, mul_assoc]
  change matrixConjugationTangent A (L X) = -L (matrixConjugationTangent A X)
  rw [matrixConjugationTangent_apply, matrixConjugationTangent_apply, map_sub, hm, hm, hA, neg_sub]

theorem abs_det_matrixConjugationOrbitTangent {A : Mat} {u : Matˣ}
    (hu : Commute (u : Mat) A) (hT : T[A] ≤ (T[A]).comap (matrixConjugationLinearEquiv u).toLinearMap) :
    |LinearMap.det ((matrixConjugationLinearEquiv u).toLinearMap.restrict (p := T[A]) (q := T[A]) hT)| = 1 :=
  abs_det_restrict_matrixOrbitTangent_of_intertwines A (matrixConjugationLinearEquiv u).toLinearMap
    (c := 1) abs_one (matrixTraceBilin_units_conj u)
    (fun X => by simpa only [one_smul, LinearEquiv.coe_coe] using matrixConjugationTangent_conjugation hu X) hT

theorem abs_det_matrixAdjustedTransposeOrbitTangent {A : Mat} {q : Matˣ}
    (hq : q.val * A * q.inv = Aᵀ)
    (hT : T[A] ≤ (T[A]).comap (matrixAdjustedTransposeLinearEquiv q).toLinearMap) :
    |LinearMap.det ((matrixAdjustedTransposeLinearEquiv q).toLinearMap.restrict (p := T[A]) (q := T[A]) hT)| = 1 :=
  abs_det_restrict_matrixOrbitTangent_of_intertwines A (matrixAdjustedTransposeLinearEquiv q).toLinearMap
    (c := -1) (by simp)
    (fun X Y => (matrixTraceBilin_units_conj q⁻¹ Xᵀ Yᵀ).trans (matrixTraceBilin_transpose X Y))
    (fun X => by simpa only [neg_one_smul, LinearEquiv.coe_coe] using matrixConjugationTangent_adjustedTranspose hq X) hT

end Langlands
