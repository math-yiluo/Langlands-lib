import Langlands.Analysis.HilbertSchmidtEvaluationProof
import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalSmoothTraceClassReduction
import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalTraceClassFromUniformBoundStatement
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Representation.Unitary.IntegratedConvolutionProof

/-! # Trace class from uniform evaluation on the full cuspidal space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis
open OperatorIdeals

/-- Uniform bounds for continuous representatives make every cuspidal operator `R(f)`
Hilbert–Schmidt by the uniform evaluation criterion; the Dixmier–Malliavin convolution
reduction then makes it trace class. -/
theorem groupSchemeFullAEL2CuspidalTraceClassFromUniformBound :
    GroupSchemeFullAEL2CuspidalTraceClassFromUniformBoundStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _
  dsimp only
  intro hSmoothing
  let Q := PositiveRationalQuotient F G T i
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let j := fullAEL2CuspidalInclusionLI F G hPD hG T i hi I e hc
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let : μQ.IsOpenPosMeasure := haarQuotientMeasure_isOpenPosMeasure F G T i hi I e hc
  let : IsFiniteMeasure μQ :=
    (positiveRationalQuotientHaarMeasure_isFiniteMeasure_iff F G T i hi I e hc).mpr
      (connectedReductiveFiniteVolume F G hG)
  apply groupSchemeFullAEL2CuspidalSmoothTraceClass_of_convolution
    integratedActionConvolution F G hPD hG T i hi I e hc
  intro f hf htest
  let R := fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf
  let A := j.toContinuousLinearMap.comp R
  obtain ⟨C, hC, hrep⟩ := hSmoothing f hf htest
  choose v hv hbound using hrep
  change ∀ z : S, (A z : Q → ℂ) =ᵐ[μQ] v z at hv
  let eval (q : Q) : S →ₗ[ℂ] ℂ := {
    toFun z := v z q
    map_add' x y := by
      have heq : (v (x + y) : Q → ℂ) =ᵐ[μQ] fun q => v x q + v y q := by
        filter_upwards [hv (x + y), hv x, hv y, Lp.coeFn_add (A x) (A y)] with q hxy hx hy h
        rw [← hxy, ← hx, ← hy, map_add]
        exact h
      exact congrFun (Measure.eq_of_ae_eq heq (v (x + y)).continuous
        ((v x).continuous.add (v y).continuous)) q
    map_smul' c x := by
      have heq : (v (c • x) : Q → ℂ) =ᵐ[μQ] fun q => c • v x q := by
        filter_upwards [hv (c • x), hv x, Lp.coeFn_smul c (A x)] with q hcx hx h
        rw [← hcx, ← hx, map_smul]
        exact h
      exact congrFun (Measure.eq_of_ae_eq heq (v (c • x)).continuous
        ((v x).continuous.const_smul c)) q }
  let k (q : Q) : S →L[ℂ] ℂ := (eval q).mkContinuous C (fun z => hbound z q)
  have hk : ∀ᵐ q ∂μQ, ‖k q‖ ≤ C :=
    Eventually.of_forall fun q => (k q).opNorm_le_bound hC (fun z => hbound z q)
  obtain ⟨idx, b, hb⟩ := (hilbertSchmidtUniformEvaluation.{u, u, u} S Q μQ A k C hC hv hk).1
  refine ⟨idx, b, ?_⟩
  simpa only [A, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    j.norm_map] using hb

end Langlands.Automorphic.GroupSchemeFunctions
