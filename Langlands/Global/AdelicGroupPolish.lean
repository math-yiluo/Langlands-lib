import Langlands.Global.AdelesSecondCountable
import Langlands.Global.AdelicGroupQuotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.MetricSpace.Polish

/-! # Polish topology on actual finite-type adelic group points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Topology TopologicalSpace
open scoped CategoryTheory.MonObj Uniformity

namespace Langlands.Global

/-- A second-countable locally compact Hausdorff topological group is Polish. -/
theorem locallyCompactGroup_polishSpace (H : Type v) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T0Space H] [LocallyCompactSpace H]
    [SecondCountableTopology H] : PolishSpace H := by
  let : UniformSpace H := IsTopologicalGroup.leftUniformSpace H
  let : IsLeftUniformGroup H := { uniformity_eq := rfl }
  have : (𝓤 H).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  have : CompleteSpace H :=
    IsLeftUniformGroup.completeSpace_of_weaklyLocallyCompactSpace H
  infer_instance

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

namespace FiniteAdelicGroupPoints

/-- Actual finite-type finite adelic points are second countable. -/
instance secondCountableTopology : SecondCountableTopology (FiniteAdelicGroupPoints F G) := by
  let : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) :=
    finiteAdeles_secondCountableTopology F
  exact G.affinePointsSecondCountableTopology (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))

/-- Actual finite-type finite adelic points are Polish. -/
instance polishSpace : PolishSpace (FiniteAdelicGroupPoints F G) :=
  locallyCompactGroup_polishSpace _

end FiniteAdelicGroupPoints

namespace InfiniteAdelicGroupPoints

/-- Actual finite-type archimedean points are second countable. -/
instance secondCountableTopology : SecondCountableTopology (InfiniteAdelicGroupPoints F G) := by
  let : SecondCountableTopology (InfiniteAdeleRing F) :=
    infiniteAdeles_secondCountableTopology F
  exact G.affinePointsSecondCountableTopology (CommAlgCat.of F (InfiniteAdeleRing F))

/-- Actual finite-type archimedean points are Polish. -/
instance polishSpace : PolishSpace (InfiniteAdelicGroupPoints F G) :=
  locallyCompactGroup_polishSpace _

end InfiniteAdelicGroupPoints

namespace AdelicGroupPoints

/-- Actual finite-type full adelic points are second countable. -/
instance secondCountableTopology : SecondCountableTopology (AdelicGroupPoints F G) := by
  let : SecondCountableTopology (AdeleRing (𝓞 F) F) := adeles_secondCountableTopology F
  exact G.affinePointsSecondCountableTopology (CommAlgCat.of F (AdeleRing (𝓞 F) F))

/-- Actual finite-type full adelic points are Polish. -/
instance polishSpace : PolishSpace (AdelicGroupPoints F G) :=
  locallyCompactGroup_polishSpace _

/-- The actual norm-one subgroup has the second-countable subtype topology. -/
instance normOneSecondCountableTopology : SecondCountableTopology (normOneSubgroup F G) :=
  secondCountableTopology_induced _ (AdelicGroupPoints F G)
    (fun x : normOneSubgroup F G => (x : AdelicGroupPoints F G))

/-- The actual norm-one subgroup is Polish as a closed subspace. -/
instance normOnePolishSpace : PolishSpace (normOneSubgroup F G) :=
  (isClosed_normOneSubgroup F G).polishSpace

/-- The actual full rational homogeneous quotient is second countable. -/
instance rationalQuotientSecondCountableTopology :
    SecondCountableTopology (RationalQuotient F G) :=
  (LeftCosetSpace.isOpenQuotientMap_mk (rationalSubgroup F G)).secondCountableTopology

/-- The actual norm-one rational homogeneous quotient is second countable. -/
instance normOneRationalQuotientSecondCountableTopology :
    SecondCountableTopology (NormOneRationalQuotient F G) :=
  (LeftCosetSpace.isOpenQuotientMap_mk (rationalNormOneSubgroup F G)).secondCountableTopology

/-- A chosen complete metric inducing the existing norm-one subgroup topology. -/
@[instance_reducible]
def normOneCompleteMetricSpace : MetricSpace (normOneSubgroup F G) :=
  completelyMetrizableMetric (normOneSubgroup F G)

theorem normOneCompleteMetricSpace_toTopologicalSpace :
    (normOneCompleteMetricSpace F G).toUniformSpace.toTopologicalSpace =
      inferInstanceAs (TopologicalSpace (normOneSubgroup F G)) := rfl

theorem normOneCompleteMetricSpace_complete :
    @CompleteSpace (normOneSubgroup F G) (normOneCompleteMetricSpace F G).toUniformSpace :=
  complete_completelyMetrizableMetric (normOneSubgroup F G)

end AdelicGroupPoints

end Langlands.Global
