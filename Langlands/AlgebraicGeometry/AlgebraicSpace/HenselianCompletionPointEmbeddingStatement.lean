import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Rational points over a henselian field and over its completion

Conrad's Proposition 5.11(2): for a quasi-separated algebraic space locally of finite
type over a henselian valued field `K`, the natural map `X(K) → X_{K̂}(K̂)` to the
rational points of the base change to the completion is a topological embedding for the
étale-chart topologies over `K` and over `K̂`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Proposition 5.11(2) (printed p.18): over a henselian valued field `K`, for
every quasi-separated algebraic space `X` locally of finite type over `Spec K`, the map
`X(K) → X_{K̂}(K̂)`, viewing a rational point as a `K̂`-valued point along `K → K̂` and
then as a rational point of the base change to `Spec K̂`, is a topological embedding for
the étale-chart topologies over `K` and over the completion `K̂`. -/
def HenselianCompletionPointEmbeddingStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)), IsQuasiSeparatedLocallyFiniteType K X →
      @Topology.IsEmbedding _ _ (etaleChartTopology K X)
        (etaleChartTopology (UniformSpace.Completion K)
          (baseChange (Spec.algebraMap K (UniformSpace.Completion K)) X))
        (fun x : RingPoints K X K =>
          (baseChangeRingPointsEquiv K (UniformSpace.Completion K)
              (UniformSpace.Completion K) X).symm
            (RingPoints.changeRing (Algebra.ofId K (UniformSpace.Completion K)) x))

end Langlands.AlgebraicGeometry.AlgebraicSpace
