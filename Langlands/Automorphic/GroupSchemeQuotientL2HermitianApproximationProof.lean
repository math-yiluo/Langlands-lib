import Langlands.Automorphic.GroupSchemeQuotientL2HermitianApproximationStatement
import Langlands.Representation.Unitary.RightHaarHermitianApproximationProof

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- Specialize actual right-Haar approximation to the original quotient action. -/
theorem groupSchemeQuotientL2HermitianApproximation :
    GroupSchemeQuotientL2HermitianApproximationStatement.{u} := by
  intro F _ _ G _ _ T i hi _ I _ e hc _
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let π := haarQuotientL2BoundedRightAction F G T i hi I e hc
  have hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y :=
    fun a => (LinearMap.norm_map_iff_inner_map_map (π a)).1
      (norm_haarQuotientL2BoundedRightAction F G T i hi I e hc a)
  have hπcont : ∀ x, Continuous (fun a => π a x) :=
    fun x => (haarQuotientL2OrbitMap F G T i hi I e hc x).continuous
  obtain ⟨f, hf, hweights, hsupport, hoperators, hlimit, _⟩ :=
    rightHaarHermitianApproximation μG π hπinner hπcont
  exact ⟨f, hf, hweights, hsupport, hoperators, hlimit⟩

end Langlands.Automorphic.GroupSchemeFunctions
