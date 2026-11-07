import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2HermitianApproximationStatement
import Langlands.Representation.Unitary.RightHaarHermitianApproximationProof

/-! # Hermitian approximation of the right action on `L²([G])`: proof -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis

set_option maxHeartbeats 1000000 in
/-- Specialize actual right-Haar approximation to the `[G]` right action. -/
theorem quotientL2HermitianApproximation : QuotientL2HermitianApproximationStatement := by
  intro F _ _ G _ _ S j T i h hi _ hc hT _ hInv'
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let π := rationalQuotientL2BoundedRightAction F G (quotientHaarMeasure F G S j) hInv'
  have hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y :=
    fun a => (LinearMap.norm_map_iff_inner_map_map (π a)).1
      (norm_rationalQuotientL2BoundedRightAction F G _ hInv' a)
  have hπcont : ∀ x, Continuous (fun a => π a x) :=
    fun x => (rationalQuotientL2OrbitMap F G hInv' h hi hc hT x).continuous
  obtain ⟨f, hf, hweights, hsupport, hoperators, hlimit, _⟩ :=
    rightHaarHermitianApproximation μG π hπinner hπcont
  exact ⟨f, hf, hweights, hsupport, hoperators, hlimit⟩

end Langlands.Global.RestrictionSplitCentre
