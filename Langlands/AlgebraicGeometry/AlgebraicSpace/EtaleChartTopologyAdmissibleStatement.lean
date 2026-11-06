import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement

/-!
# The étale-chart topology is the topology of Conrad's Proposition 5.4

Conrad's existence proof of Proposition 5.4: over a henselian valued field, the strongest
topology on rational points making every map from the rational points of an étale chart
of finite type continuous has all the properties of the corrected proposition, and it is
the only such family on quasi-separated, locally separated, locally finite type spaces.
-/

universe u

open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's proof of Proposition 5.4 (printed p.15), restricted to locally separated
spaces: over a henselian valued field the étale-chart topology is admissible, every
admissible family agrees with it on quasi-separated, locally separated, locally finite
type spaces, and it has the separated-space properties. -/
def EtaleChartTopologyAdmissibleStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    IsAdmissibleRationalPointTopology K (etaleChartTopology K) ∧
      (∀ τ' : ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)),
          TopologicalSpace (RingPoints K X K),
        IsAdmissibleRationalPointTopology K τ' →
          ∀ X, IsLocallySeparatedLocallyFiniteType K X → τ' X = etaleChartTopology K X) ∧
      SeparatedRationalPointTopologyProperties K (etaleChartTopology K)

end Langlands.AlgebraicGeometry.AlgebraicSpace
