import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionPointMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement

/-! # Closed rational loci over extensions of complete normed fields -/
noncomputable section
universe u
open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The complete-field separated-space closed-image core of the henselian extension
point theorem. The normed extension may have arbitrary degree or transcendence degree. -/
def CompleteExtensionPointClosedRangeStatement : Prop :=
  ∀ (K L : Type u) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] [CompleteSpace K] [CompleteSpace L],
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)),
      IsQuasiSeparatedLocallyFiniteType K X → IsSeparated X →
        IsClosed[etaleChartTopology L (baseChange (Spec.algebraMap K L) X)]
          (Set.range (extensionPointMap L X))

end Langlands.AlgebraicGeometry.AlgebraicSpace
