import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarStatement
import Langlands.AlgebraicGeometry.PointTopology.PointSecondCountabilityProof
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Mathlib.Topology.Metrizable.Urysohn

/-! # Haar regularity from actual finite-coordinate point topologies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory ValuativeRel TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The affine comparison transfers the finite-coordinate countable base. -/
theorem rationalPoint_secondCountableTopology
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] :
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    SecondCountableTopology (RationalPoint F G.X) := by
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  let : SecondCountableTopology F := Langlands.HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : SecondCountableTopology (RingPoint F G.X F) :=
    affineSchemePointSecondCountability F F G.X
  exact (rationalPointHomeomorph F G.X).isEmbedding.secondCountableTopology

/-- Every supplied Haar measure on the actual finite-type affine group is regular. -/
theorem rationalPointHaarRegularity : RationalPointHaarRegularityStatement.{u} := by
  intro F _ _ _ _ G _ _
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  let : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
  let : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
  let := rationalPoint_isTopologicalGroup F G
  let := rationalPoint_t2Space F G
  let := rationalPoint_locallyCompactSpace F G
  let := rationalPoint_secondCountableTopology F G
  refine ⟨inferInstance, ?_⟩
  intro mu hmu
  let := hmu
  have : PseudoMetrizableSpace (RationalPoint F G.X) := inferInstance
  have : SigmaCompactSpace (RationalPoint F G.X) := inferInstance
  have : IsLocallyFiniteMeasure mu := inferInstance
  have : SigmaFinite mu := inferInstance
  exact ⟨inferInstance, inferInstance⟩

end Langlands.AlgebraicGeometry.PointTopology
