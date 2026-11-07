import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2HermitianApproximationStatement
import Langlands.Representation.Unitary.RightHaarHermitianApproximationProof

/-! # Hermitian approximation on `L²([G])` and its cuspidal subspace: proof -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis

set_option maxHeartbeats 1000000 in
/-- One weight sequence approximates the identity on `L²([G])` and its cuspidal subspace. -/
theorem quotientFullAEL2HermitianApproximation :
    QuotientFullAEL2HermitianApproximationStatement := by
  intro F _ _ G _ _ hPD hG S j T i h hi _ hc hT _ hInv'
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let Sq := quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT
  let π := rationalQuotientL2BoundedRightAction F G (quotientHaarMeasure F G S j) hInv'
  have hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y :=
    fun a => (LinearMap.norm_map_iff_inner_map_map (π a)).1
      (norm_rationalQuotientL2BoundedRightAction F G _ hInv' a)
  have hπcont : ∀ x, Continuous (fun a => π a x) :=
    fun x => (rationalQuotientL2OrbitMap F G hInv' h hi hc hT x).continuous
  obtain ⟨f, hf, hweights, hsupport, hgeneric, hgenericLimit, _⟩ :=
    rightHaarHermitianApproximation μG π hπinner hπcont
  let A := fun n => rationalQuotientL2IntegratedAction F G hInv' h hi hc hT μG.inv
    (fun a => (f n a : ℂ)) (hf n).ofReal
  let B := fun n => quotientFullAEL2CuspidalIntegratedAction F G hPD hG h hi hc hT hInv'
    μG.inv (fun a => (f n a : ℂ)) (hf n).ofReal
  have hoperators : ∀ n, (A n).IsSymmetric ∧ ‖A n‖ ≤ 1 := hgeneric
  have hlimit : ∀ φ : Lp ℂ 2 (quotientHaarMeasure F G S j),
      Tendsto (fun n => A n φ) atTop (𝓝 φ) := hgenericLimit
  have hval : ∀ n (ψ : Sq), (B n ψ).val = A n ψ.val := fun n ψ =>
    quotientFullAEL2CuspidalIntegratedAction_val F G hPD hG h hi hc hT hInv' μG.inv
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
      quotientFullAEL2CuspidalOrthogonalProjection_integratedAction F G hPD hG h hi hc hT hInv'
        μG.inv (fun a => (f n a : ℂ)) (hf n).ofReal φ
  · exact fun n φ =>
      quotientFullAEL2CuspidalAmbientProjection_integratedAction F G hPD hG h hi hc hT hInv'
        μG.inv (fun a => (f n a : ℂ)) (hf n).ofReal φ

end Langlands.Global.RestrictionSplitCentre
