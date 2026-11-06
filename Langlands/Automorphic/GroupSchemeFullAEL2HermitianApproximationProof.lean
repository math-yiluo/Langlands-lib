import Langlands.Automorphic.GroupSchemeFullAEL2HermitianApproximationStatement
import Langlands.Automorphic.GroupSchemeQuotientL2HermitianApproximationProof

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- Transfer the original ambient approximation to its original closed full cusp carrier. -/
theorem groupSchemeFullAEL2HermitianApproximation :
    GroupSchemeFullAEL2HermitianApproximationStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  obtain ⟨f, hf, hweights, hsupport, hoperators, hlimit⟩ :=
    groupSchemeQuotientL2HermitianApproximation F G T i hi I e hc
  let A := fun n => haarQuotientL2IntegratedAction F G T i hi I e hc μG.inv
    (fun a => (f n a : ℂ)) (hf n).ofReal
  let B := fun n => fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG.inv
    (fun a => (f n a : ℂ)) (hf n).ofReal
  have hval : ∀ n (ψ : S), (B n ψ).val = A n ψ.val := fun n ψ =>
    fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc μG.inv
      (fun a => (f n a : ℂ)) (hf n).ofReal ψ
  refine ⟨f, hf, hweights, hsupport, hoperators, hlimit, ?_, ?_, hval, ?_, ?_⟩
  · intro n
    constructor
    · intro ψ χ
      change inner ℂ (B n ψ).val χ.val = inner ℂ ψ.val (B n χ).val
      rw [hval, hval]
      exact (hoperators n).1 ψ.val χ.val
    · apply (B n).opNorm_le_bound (by norm_num)
      intro ψ
      calc
        ‖B n ψ‖ = ‖A n ψ.val‖ := congrArg norm (hval n ψ)
        _ ≤ ‖A n‖ * ‖ψ.val‖ := (A n).le_opNorm ψ.val
        _ ≤ 1 * ‖ψ‖ := mul_le_mul_of_nonneg_right (hoperators n).2 (norm_nonneg _)
  · intro ψ
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n => (B n ψ).val) atTop (𝓝 ψ.val)
    simpa only [hval] using hlimit ψ.val
  · exact fun n φ =>
      fullAEL2CuspidalOrthogonalProjection_integratedAction F G hPD hG T i hi I e hc μG.inv
        (fun a => (f n a : ℂ)) (hf n).ofReal φ
  · exact fun n φ =>
      fullAEL2CuspidalAmbientProjection_integratedAction F G hPD hG T i hi I e hc μG.inv
        (fun a => (f n a : ℂ)) (hf n).ofReal φ

end Langlands.Automorphic.GroupSchemeFunctions
