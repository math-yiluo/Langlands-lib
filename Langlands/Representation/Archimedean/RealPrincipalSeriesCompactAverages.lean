import Langlands.Representation.Archimedean.OrthogonalPolynomialConvolution
import Langlands.Representation.Archimedean.RealPrincipalSeriesHilbertAction

/-! # Finite-rank compact averages on the real principal-series Hilbert space -/

noncomputable section

open Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open OrthogonalFinitePolynomial RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK borelSpaceK
attribute [local instance] OrthogonalFinitePolynomial.secondCountableTopology_orthogonal

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "K" => unitaryCompact ℝ n
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ

/-- The orthogonal matrices and the orthogonal subgroup of the matrix units are the same group. -/
def orthogonalCompactEquiv (n : ℕ) : Matrix.unitaryGroup (Fin n) ℝ ≃* unitaryCompact ℝ n where
  toFun k := ⟨Unitary.toUnits k, k.2⟩
  invFun k := ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Units.ext rfl)
  map_mul' k l := Subtype.ext (Unitary.toUnits.map_mul k l)

theorem continuous_orthogonalCompactEquiv : Continuous (orthogonalCompactEquiv n) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
  exact continuous_star.comp continuous_subtype_val

theorem continuous_orthogonalCompactEquiv_symm : Continuous (orthogonalCompactEquiv n).symm :=
  (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

/-- Haar probability measure on the orthogonal matrices. -/
def haarOrthogonal (n : ℕ) : Measure (Matrix.unitaryGroup (Fin n) ℝ) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance isHaarMeasure_haarOrthogonal (n : ℕ) : (haarOrthogonal n).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

instance isProbabilityMeasure_haarOrthogonal (n : ℕ) : IsProbabilityMeasure (haarOrthogonal n) :=
  ⟨Measure.haarMeasure_self⟩

variable (a : Fin n → ℂ) (e : Fin n → Fin 2)

private theorem continuous_orthogonalInclusion : Continuous (Unitary.toUnits : O → GL) :=
  continuous_subtype_val.comp (continuous_orthogonalCompactEquiv (n := n))

private theorem continuous_orthogonalAction :
    Continuous (fun p : O × Hilbert a e => representation a e (Unitary.toUnits p.1) p.2) := by
  have hA : Continuous (fun p : GL × Hilbert a e => representation a e p.1 p.2) :=
    isContinuousRepresentation a e
  have hB : Continuous (fun p : O × Hilbert a e => (Unitary.toUnits p.1, p.2)) :=
    (continuous_orthogonalInclusion.comp continuous_fst).prodMk continuous_snd
  have h := hA.comp hB
  simpa only [Function.comp_def] using h

/-- Average the compact action on the principal-series Hilbert completion. -/
def orthogonalAverage (φ : C(O, ℂ)) : Hilbert a e →L[ℂ] Hilbert a e :=
  compactAverage (E := Hilbert a e) (A := fun k : O => representation a e (Unitary.toUnits k))
    (haarOrthogonal n) (continuous_orthogonalAction a e) φ

@[simp]
theorem orthogonalAverage_apply (φ : C(O, ℂ)) (x : Hilbert a e) :
    orthogonalAverage a e φ x = ∫ k, φ k • representation a e (Unitary.toUnits k) x ∂haarOrthogonal n :=
  rfl

private def restrictionOrthogonal (f : PrincipalSeries a e) : C(O, ℂ) :=
  (compactRestriction a e f).comp ⟨orthogonalCompactEquiv n, continuous_orthogonalCompactEquiv⟩

private def orthogonalProfilePullback : C(O, ℂ) →L[ℂ] C(K, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ
    ⟨(orthogonalCompactEquiv n).symm, continuous_orthogonalCompactEquiv_symm⟩

private def orthogonalProfileToL2 : C(O, ℂ) →L[ℂ] Lp ℂ 2 (haarK n) :=
  (ContinuousMap.toLp 2 (haarK n) ℂ).comp (orthogonalProfilePullback (n := n))

private def translatedRestriction (f : PrincipalSeries a e) (k : O) : C(K, ℂ) :=
  compactRestriction a e (translation a e (Unitary.toUnits k) f)

private theorem continuous_translatedRestriction (f : PrincipalSeries a e) :
    Continuous (translatedRestriction a e f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : O × K => f.1 ((p.2 : GL) * Unitary.toUnits p.1))
  exact f.2.1.continuous.comp ((continuous_subtype_val.comp continuous_snd).mul
    (continuous_orthogonalInclusion.comp continuous_fst))

private theorem integrable_weighted_translatedRestriction (φ : C(O, ℂ)) (f : PrincipalSeries a e) :
    Integrable (fun k : O => φ k • translatedRestriction a e f k) (haarOrthogonal n) :=
  OrthogonalFinitePolynomial.integrable_of_continuous _
    (φ.continuous.smul (continuous_translatedRestriction a e f))

private theorem integral_weighted_translatedRestriction (φ : C(O, ℂ)) (f : PrincipalSeries a e) :
    (∫ k : O, φ k • translatedRestriction a e f k ∂haarOrthogonal n) =
      orthogonalProfilePullback (n := n)
        (convolution (haarOrthogonal n) φ (restrictionOrthogonal a e f)) := by
  apply ContinuousMap.ext
  intro k
  let ev := ContinuousMap.evalCLM ℂ (M := ℂ) k
  have h := (ev.integral_comp_comm (integrable_weighted_translatedRestriction a e φ f)).symm
  change ev (∫ t : O, φ t • translatedRestriction a e f t ∂haarOrthogonal n) =
    convolution (haarOrthogonal n) φ (restrictionOrthogonal a e f) ((orthogonalCompactEquiv n).symm k)
  rw [h, convolution_apply]
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  change φ t * f.1 ((k : GL) * Unitary.toUnits t) =
    φ t * f.1 (((orthogonalCompactEquiv n) ((orthogonalCompactEquiv n).symm k * t) : K) : GL)
  rw [map_mul, MulEquiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem coe_orthogonalAverage_embed (φ : C(O, ℂ)) (f : PrincipalSeries a e) :
    (closureSubmodule a e).subtypeL (orthogonalAverage a e φ (embed a e f)) =
      orthogonalProfileToL2 (n := n)
        (convolution (haarOrthogonal n) φ (restrictionOrthogonal a e f)) := by
  let J : Hilbert a e →L[ℂ] Lp ℂ 2 (haarK n) := (closureSubmodule a e).subtypeL
  let L : C(K, ℂ) →L[ℂ] Lp ℂ 2 (haarK n) := ContinuousMap.toLp 2 (haarK n) ℂ
  let x := embed a e f
  let F : O → Hilbert a e := fun k => φ k • representation a e (Unitary.toUnits k) x
  let P : O → C(K, ℂ) := fun k => φ k • translatedRestriction a e f k
  have hIn : Continuous (fun k : O => (k, x)) := continuous_id.prodMk continuous_const
  have hA : Continuous (fun k : O => representation a e (Unitary.toUnits k) x) := by
    have h := (continuous_orthogonalAction a e).comp hIn
    simpa only [Function.comp_def] using h
  have hF : Integrable F (haarOrthogonal n) :=
    OrthogonalFinitePolynomial.integrable_of_continuous _ (φ.continuous.smul hA)
  have hP : Integrable P (haarOrthogonal n) := integrable_weighted_translatedRestriction a e φ f
  have hEq (k : O) : J (F k) = L (P k) := by
    change J (φ k • representation a e (Unitary.toUnits k) x) =
      L (φ k • translatedRestriction a e f k)
    rw [map_smul, map_smul, representation_embed]
    rfl
  calc
    _ = J (∫ k, F k ∂haarOrthogonal n) := congrArg J (orthogonalAverage_apply a e φ x)
    _ = ∫ k, J (F k) ∂haarOrthogonal n := (J.integral_comp_comm hF).symm
    _ = ∫ k, L (P k) ∂haarOrthogonal n := integral_congr_ae (Eventually.of_forall hEq)
    _ = L (∫ k, P k ∂haarOrthogonal n) := L.integral_comp_comm hP
    _ = _ := congrArg L (integral_weighted_translatedRestriction a e φ f)

/-- Polynomial compact averages have finite-dimensional range in the Hilbert completion. -/
theorem finiteDimensional_orthogonalAverage_range {φ : C(O, ℂ)} (hφ : φ ∈ polynomialStar n) :
    FiniteDimensional ℂ (LinearMap.range (orthogonalAverage a e φ).toLinearMap) := by
  let J := (closureSubmodule a e).subtypeL
  let W := (LinearMap.range (convolution (haarOrthogonal n) φ).toLinearMap).map
    (orthogonalProfileToL2 (n := n)).toLinearMap
  have hConv := finiteDimensional_convolution_range (haarOrthogonal n) hφ
  have hW : FiniteDimensional ℂ W := inferInstance
  have hclosedW : IsClosed (W : Set (Lp ℂ 2 (haarK n))) := W.closed_of_finiteDimensional
  have hclosed : IsClosed ((J.comp (orthogonalAverage a e φ)) ⁻¹' (W : Set (Lp ℂ 2 (haarK n)))) :=
    hclosedW.preimage (J.comp (orthogonalAverage a e φ)).continuous
  have hle : Set.range (embed a e) ⊆ (J.comp (orthogonalAverage a e φ)) ⁻¹' (W : Set (Lp ℂ 2 (haarK n))) := by
    rintro _ ⟨f, rfl⟩
    change (closureSubmodule a e).subtypeL (orthogonalAverage a e φ (embed a e f)) ∈ W
    rw [coe_orthogonalAverage_embed]
    exact ⟨_, ⟨restrictionOrthogonal a e f, rfl⟩, rfl⟩
  have hall (x : Hilbert a e) : J (orthogonalAverage a e φ x) ∈ W :=
    closure_minimal hle hclosed (denseRange_embed a e x)
  let U := LinearMap.range (orthogonalAverage a e φ).toLinearMap
  let T : U →ₗ[ℂ] W := (J.toLinearMap.comp U.subtype).codRestrict W (by
    rintro ⟨y, ⟨x, rfl⟩⟩
    exact hall x)
  have hinj : Function.Injective T := by
    intro x y h
    have he := congrArg (fun z : W => (z : Lp ℂ 2 (haarK n))) h
    apply Subtype.ext
    apply Subtype.ext
    exact he
  exact FiniteDimensional.of_injective T hinj

end Langlands.Archimedean.RealPrincipalSeriesHilbert
