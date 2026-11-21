import Langlands.Analysis.TraceTestDistribution
import Langlands.Representation.Archimedean.RealFrobeniusTraceClass
import Mathlib.MeasureTheory.Group.Integral

/-! # Conjugation-invariant character distributions of real Hilbert actions -/

noncomputable section

open Filter MeasureTheory Set
open scoped Distributions InnerProductSpace Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.Analysis.OperatorIdeals
open Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

variable {n : ℕ}

local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

local instance : SecondCountableTopology GL := Units.isOpenEmbedding_val.secondCountableTopology

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [IsFiniteMeasureOnCompacts μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H)) (hR : IsContinuousRepresentation R)

include hR in
theorem integrable_realTestOrbit (φ : Test n) (x : H) :
    Integrable (fun g : GL => (φ (g : Mat) : ℂ) • R g x) μ := by
  have hCont : Continuous (fun g : GL => R g x) :=
    hR.comp (continuous_id.prodMk continuous_const)
  have h := (RealPrincipalSeriesHilbert.complexRestriction φ).continuous.smul hCont
  exact h.integrable_of_hasCompactSupport
    (RealPrincipalSeriesHilbert.hasCompactSupport_complexRestriction φ).smul_right

variable [CompleteSpace H] (T : Test n →ₗ[ℝ] H →L[ℂ] H)
  (hT : ∀ (φ : Test n) (x : H), T φ x = ∫ g : Langlands.GeneralLinear n ℝ,
    (φ (g : Matrix (Fin n) (Fin n) ℝ) : ℂ) • R g x ∂μ)

include hR hT in
theorem continuous_realIntegratedCoefficient (u v : H) :
    Continuous (fun φ : Test n => ⟪u, T φ v⟫_ℂ) := by
  borelize Mat
  let : LocallyCompactSpace Mat := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  let j : GL → Mat := Units.val
  have hj : MeasurableEmbedding j := Units.isOpenEmbedding_val.measurableEmbedding
  let c : GL → ℂ := fun g => ⟪u, R g v⟫_ℂ
  have hc : Continuous c :=
    (innerSL ℂ u).continuous.comp (hR.comp (continuous_id.prodMk continuous_const))
  let f := unitsExtension c
  have hfc (g : GL) : f (j g) = c g := unitsExtension_val c g
  have hLoc : LocallyIntegrableOn f (matrixOpen n : Set Mat) (μ.map j) := by
    apply (locallyIntegrableOn_iff (matrixOpen n).isOpen.isLocallyClosed).mpr
    intro S hS hC
    have hS' : S ⊆ Set.range j := by
      change S ⊆ Set.range (Units.val : GL → Mat)
      rw [range_val_eq_setOf_isUnit]
      exact hS
    have hC' : IsCompact (j ⁻¹' S) :=
      Units.isOpenEmbedding_val.isInducing.isCompact_preimage' hC hS'
    rw [IntegrableOn, Measure.restrict_map hj.measurable hC.isClosed.measurableSet, hj.integrable_map_iff]
    have he : f ∘ j = c := funext hfc
    rw [he]
    exact hc.continuousOn.integrableOn_compact hC'
  apply (_root_.Distribution.ofFun (matrixOpen n) f (μ.map j) ⊤).continuous.congr
  intro φ
  rw [_root_.Distribution.ofFun_apply hLoc, hj.integral_map, hT]
  have hI := integrable_realTestOrbit μ R hR φ v
  change (∫ g : GL, φ (j g) • f (j g) ∂μ) =
    (innerSL ℂ u) (∫ g : GL, (φ (g : Mat) : ℂ) • R g v ∂μ)
  rw [← (innerSL ℂ u).integral_comp_comm hI]
  apply integral_congr_ae
  exact Eventually.of_forall fun g => by
    change φ (j g) • f (j g) = ⟪u, (φ (j g) : ℂ) • R g v⟫_ℂ
    rw [hfc]
    exact (inner_smul_real_right u (R g v) (φ (j g))).symm

variable (hTrace : ∀ φ, IsTraceClass (T φ))

/-- The distributional character of a trace-class integrated real Hilbert action. -/
def realHilbertCharacter : Distribution n :=
  traceTestDistribution T hTrace (fun x => continuous_realIntegratedCoefficient μ R hR T hT x x)

@[simp]
theorem realHilbertCharacter_apply (φ : Test n) :
    realHilbertCharacter μ R hR T hT hTrace φ = operatorTrace (T φ) := rfl

variable [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

include hR hT in
/-- Pullback of a test by conjugation acts on the integrated operator by inverse conjugation. -/
theorem realIntegratedOperator_conjugation (g : GL) (φ : Test n) :
    T (conjugationTest g φ) = ((R g⁻¹).comp (T φ)).comp (R g) := by
  apply ContinuousLinearMap.ext
  intro x
  let F : GL → H := fun h => R g⁻¹ ((φ (h : Mat) : ℂ) • R h (R g x))
  calc
    T (conjugationTest g φ) x = ∫ h : GL, F (g * h * g⁻¹) ∂μ := by
      rw [hT]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro h
      simp only [F, conjugationTest_apply, Units.val_mul, map_smul]
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
      have he : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      rw [he]
    _ = ∫ h : GL, F h ∂μ := by
      rw [integral_mul_left_eq_self (fun h => F (h * g⁻¹)) g, integral_mul_right_eq_self F g⁻¹]
    _ = (((R g⁻¹).comp (T φ)).comp (R g)) x := by
      change (∫ h, F h ∂μ) = R g⁻¹ (T φ (R g x))
      rw [hT]
      exact (R g⁻¹).integral_comp_comm (integrable_realTestOrbit μ R hR φ (R g x))

/-- The distributional character of a trace-class integrated real Hilbert action
is invariant under conjugation for a left and right invariant measure. -/
theorem isConjugationInvariant_realHilbertCharacter :
    IsConjugationInvariant (realHilbertCharacter μ R hR T hT hTrace) := by
  intro g φ
  simp only [realHilbertCharacter_apply, realIntegratedOperator_conjugation μ R hR T hT]
  have hId : (R g).comp (R g⁻¹) = ContinuousLinearMap.id ℂ H := by
    ext x
    change R g (R g⁻¹ x) = x
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  have h := (operatorTraceCyclicity H H (T φ) (R g⁻¹) (R g) (hTrace φ)).2.2
  simpa only [hId, ContinuousLinearMap.comp_id] using h

end Langlands.Archimedean
