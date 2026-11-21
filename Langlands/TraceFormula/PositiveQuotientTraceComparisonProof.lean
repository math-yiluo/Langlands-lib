import Langlands.TraceFormula.PositiveQuotientTraceComparisonStatement
import Langlands.Analysis.Local.QuotientProductFactor
import Langlands.Analysis.OperatorTraceProof

/-! # Proof of the positive-quotient trace comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

private theorem pullback_congr {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μX : Measure X} {μY : Measure Y} {r s : X → Y} (hr : MeasurePreserving r μX μY)
    (hs : MeasurePreserving s μX μY) (h : r = s) (v : Lp ℂ 2 μY) :
    Lp.compMeasurePreserving r hr v = Lp.compMeasurePreserving s hs v := by
  subst s
  rfl

/-- Pullback along a measure-preserving equivalence, with inverse pullback along its inverse. -/
private def pullbackEquiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μX : Measure X} {μY : Measure Y} (j : X ≃ᵐ Y) (hj : MeasurePreserving j μX μY) :
    Lp ℂ 2 μY ≃ₗᵢ[ℂ] Lp ℂ 2 μX := by
  let hj' := hj.symm j
  refine LinearIsometryEquiv.ofLinearIsometry (Lp.compMeasurePreservingₗᵢ ℂ j hj)
    (Lp.compMeasurePreservingₗᵢ ℂ j.symm hj').toLinearMap
    (LinearMap.ext fun w => ?_) (LinearMap.ext fun v => ?_)
  · change Lp.compMeasurePreserving j hj (Lp.compMeasurePreserving j.symm hj' w) = w
    rw [← Lp.compMeasurePreserving_comp_apply,
      pullback_congr _ (MeasurePreserving.id _) j.symm_comp_self]
    exact Lp.compMeasurePreserving_id_apply w
  · change Lp.compMeasurePreserving j.symm hj' (Lp.compMeasurePreserving j hj v) = v
    rw [← Lp.compMeasurePreserving_comp_apply,
      pullback_congr _ (MeasurePreserving.id _) j.self_comp_symm]
    exact Lp.compMeasurePreserving_id_apply v

private theorem traceComparison_of_intertwines {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : E ≃ₗᵢ[ℂ] H) (A : E →L[ℂ] E) (B : H →L[ℂ] H)
    (hU : ∀ v, U (A v) = B (U v)) :
    (IsTraceClass A ↔ IsTraceClass B) ∧
      (IsTraceClass A → operatorTrace A = operatorTrace B) := by
  let C := U.toLinearIsometry.toContinuousLinearMap
  let D := U.symm.toLinearIsometry.toContinuousLinearMap
  have hB : (C.comp A).comp D = B := by
    apply ContinuousLinearMap.ext
    intro w
    change U (A (U.symm w)) = B w
    rw [hU, U.apply_symm_apply]
  have hA : (D.comp B).comp C = A := by
    apply ContinuousLinearMap.ext
    intro v
    change U.symm (B (U v)) = A v
    rw [← hU, U.symm_apply_apply]
  have hDC : A.comp (D.comp C) = A := by
    apply ContinuousLinearMap.ext
    intro v
    change A (U.symm (U v)) = A v
    rw [U.symm_apply_apply]
  have forward (h : IsTraceClass A) :
      IsTraceClass B ∧ operatorTrace A = operatorTrace B := by
    obtain ⟨h₁, _, h₂⟩ := operatorTraceCyclicity E H A C D h
    rw [hB] at h₁ h₂
    rw [hDC] at h₂
    exact ⟨h₁, h₂.symm⟩
  refine ⟨⟨fun h => (forward h).1, ?_⟩, fun h => (forward h).2⟩
  intro h
  rw [← hA]
  exact (operatorTraceCyclicity H E B D C h).1

/-- Averaging over the actual positive factor gives the stated trace-class and trace comparison. -/
theorem positiveQuotientTraceComparison : PositiveQuotientTraceComparisonStatement.{u} := by
  intro F _ _ G _ _ T i hi _ I _ e hc _ f
  let μA := normalizedPositiveHaarMeasure F G T i hi I e hc
  let : μA.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F G T i hi I e hc
  let : SigmaFinite μA := normalizedPositiveHaarMeasure_sigmaFinite F G T i hi I e hc
  let μN : Measure (normOneSubgroup F G) := Measure.haar
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let d := normOneDecomposition F G T i hi I e
  let fOne := Langlands.QuotientIntegration.compactIntegralFullFactor _ μA
    (f.comp d.toCocompactMap)
  refine ⟨fOne.continuous, fOne.hasCompactSupport, ?_⟩
  intro hf hfOne π hπnorm hπmeas hπtr
  let νP := positiveRationalQuotientHaarMeasure F G T i
  let νN := normOneRationalQuotientHaarMeasure F G
  let j := positiveQuotientMeasurableEquiv F G T i hi I e hc
  let hj : MeasurePreserving j νN νP := measurePreserving_positiveQuotient F G T i hi I e hc
  let U := pullbackEquiv j hj
  let p := normOneProjection F G T i hi I e hc
  let ρ := quotientL2RightAction F G T i νP (haarQuotientMeasureRightInvariant F G T i hi I e hc)
  have hrt (n : normOneSubgroup F G) (q : NormOneRationalQuotient F G) :
      Langlands.QuotientIntegration.rightTranslate (rationalNormOneSubgroup F G) n q =
        LeftCosetSpace.rightTranslate (rationalNormOneSubgroup F G) n q := by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalNormOneSubgroup F G) q
    rfl
  let hn := measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure F G
  have hπpull (n : normOneSubgroup F G) (w : Lp ℂ 2 νN) :
      π n w = Lp.compMeasurePreserving _ (hn n) w := by
    have h := hπtr n w
    simp only [hrt] at h
    exact Lp.ext (h.trans (Lp.coeFn_compMeasurePreserving w (hn n)).symm)
  have hU (g : AdelicGroupPoints F G) (v : Lp ℂ 2 νP) :
      U (ρ g v) = π (p g) (U v) := by
    rw [hπpull]
    change Lp.compMeasurePreserving j hj
        (Lp.compMeasurePreserving _ (haarQuotientMeasureRightInvariant F G T i hi I e hc g) v) =
      Lp.compMeasurePreserving _ (hn (p g)) (Lp.compMeasurePreserving j hj v)
    rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
    apply pullback_congr
    funext q
    exact (positiveQuotientHomeomorph_rightTranslate F G T i hi I e hc g q).symm
  apply traceComparison_of_intertwines U
  intro v
  let C := U.toLinearIsometry.toContinuousLinearMap
  let k : AdelicGroupPoints F G → Lp ℂ 2 νP := fun g => f g • ρ g v
  let l : AdelicGroupPoints F G → Lp ℂ 2 νN := fun g => C (k g)
  have hk : Integrable k μG :=
    haarQuotientL2ActionIntegrand_integrable F G T i hi I e hc _ f hf v
  have hl : Integrable l μG := C.integrable_comp hk
  have hd : MeasurePreserving d (μA.prod μN) μG :=
    measurePreserving_normOneDecomposition F G T i hi I e hc
  have hprod : Integrable (fun x => l (d x)) (μA.prod μN) :=
    (hd.integrable_comp_emb d.toMeasurableEquiv.measurableEmbedding).2 hl
  have hp (a : intrinsicSubgroup F T) (n : normOneSubgroup F G) : p (d (a, n)) = n := by
    change normOneProjection F G T i hi I e hc (d (a, n)) = n
    rw [show d (a, n) = positivePointMap F G T i a * n from rfl, map_mul,
      normOneProjection_positivePointMap, normOneProjection_normOne, one_mul]
  rw [haarQuotientL2IntegratedAction_apply, integratedIsometricAction_apply]
  calc
    U (∫ g, k g ∂μG) = ∫ g, l g ∂μG := (C.integral_comp_comm hk).symm
    _ = ∫ x, l (d x) ∂(μA.prod μN) := (hd.integral_comp' (f := d.toMeasurableEquiv) l).symm
    _ = ∫ n, ∫ a, l (d (a, n)) ∂μA ∂μN := integral_prod_symm _ hprod
    _ = ∫ n, fOne n • π n (U v) ∂μN := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun n => by
        calc
          (∫ a, l (d (a, n)) ∂μA) = ∫ a, f (d (a, n)) • π n (U v) ∂μA := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun a => by
              change C (f (d (a, n)) • ρ (d (a, n)) v) = _
              rw [map_smul]
              change f (d (a, n)) • U (ρ (d (a, n)) v) = _
              rw [hU, hp]
          _ = fOne n • π n (U v) := integral_smul_const _ _

end Langlands.TraceFormula
