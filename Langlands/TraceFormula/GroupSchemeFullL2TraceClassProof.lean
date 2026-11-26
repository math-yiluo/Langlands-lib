import Langlands.TraceFormula.GroupSchemeFullL2TraceClassStatement
import Langlands.TraceFormula.GroupSchemeCuspidalImageProof
import Langlands.Representation.Unitary.IntegratedConvolutionProof
import Langlands.Analysis.HilbertSchmidtProductTraceClassProof

/-! # Trace class on the full automorphic `L²` space -/

noncomputable section

universe u

open MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.PositiveRealTorus
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis Langlands.Analysis.OperatorIdeals

namespace Langlands.TraceFormula

/-- The full convolution operator factors through the cuspidal space as a composition of
Hilbert–Schmidt maps. -/
theorem groupSchemeFullL2TraceClass : GroupSchemeFullL2TraceClassStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _ μG f₁ f₂ hHS₁ hHS₂ hvanish
  have hf₁ : Integrable f₁ μG := f₁.continuous.integrable_of_hasCompactSupport f₁.hasCompactSupport
  have hf₂ : Integrable f₂ μG := f₂.continuous.integrable_of_hasCompactSupport f₂.hasCompactSupport
  let H := Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let incl := (fullAEL2CuspidalInclusionLI F G hPD hG T i hi I e hc).toContinuousLinearMap
  let P := fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc
  let R := haarQuotientL2IntegratedAction F G T i hi I e hc μG
  let Rc := fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG
  obtain ⟨h, hconv⟩ := integratedActionConvolution (AdelicGroupPoints F G) H μG
    (haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (norm_haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (haarQuotientL2Orbit_aestronglyMeasurable F G T i hi I e hc μG) f₁ f₂ hf₁ hf₂
  change R _ h = (R f₁ hf₁).comp (R f₂ hf₂) at hconv
  have hfactor : (R f₁ hf₁).comp (R f₂ hf₂) =
      (incl.comp (Rc f₁ hf₁)).comp ((Rc f₂ hf₂).comp P) := by
    apply ContinuousLinearMap.ext
    intro v
    change R f₁ hf₁ (R f₂ hf₂ v) = incl (Rc f₁ hf₁ (Rc f₂ hf₂ (P v)))
    let w : S :=
      ⟨R f₂ hf₂ v, groupSchemeCuspidalImage F G hPD hG T i hi I e hc f₂ hf₂ hvanish v⟩
    have hPw : P (R f₂ hf₂ v) = w :=
      fullAEL2CuspidalOrthogonalProjection_inclusion F G hPD hG T i hi I e hc w
    have hw : Rc f₂ hf₂ (P v) = w :=
      (fullAEL2CuspidalOrthogonalProjection_integratedAction F G hPD hG T i hi I e hc
        μG f₂ hf₂ v).symm.trans hPw
    rw [hw]
    exact (fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc μG f₁ hf₁ w).symm
  refine ⟨h, ?_⟩
  change IsTraceClass (R _ h)
  rw [hconv, hfactor]
  exact hilbertSchmidtProductTraceClass H S _ _
    (isHilbertSchmidt_precomp _ P (hHS₂ hf₂))
    (isHilbertSchmidt_postcomp _ incl (hHS₁ hf₁))

end Langlands.TraceFormula
