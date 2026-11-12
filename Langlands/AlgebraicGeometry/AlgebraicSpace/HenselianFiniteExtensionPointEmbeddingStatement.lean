import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange

/-!
# Rational points over a finite extension of henselian valued fields

Conrad, printed p.19, in the finite-degree part of the proof of Proposition 5.11(3): for a
finite extension `K'/K` of henselian valued fields and a quasi-separated algebraic space `X`
locally of finite type over `K` whose diagonal is an immersion (so a quasi-compact immersion),
the natural map `X(K) → X_{K'}(K')` is a topological embedding for the étale-chart topologies,
without any completeness assumption.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's finite-degree supplement to Proposition 5.11(3) (printed p.19): let `K'/K` be a
finite extension of henselian valued fields, the norm of `K'` restricting to that of `K`. For
every algebraic space `X` over `Spec K` that is quasi-separated, locally separated (its
diagonal is an immersion) and locally of finite type, the map `X(K) → X_{K'}(K')`, viewing a
rational point as a `K'`-valued point and then as a rational point of the base change to
`Spec K'`, is a topological embedding for the étale-chart topologies over `K` and over `K'`. -/
def HenselianFiniteExtensionPointEmbeddingStatement : Prop :=
  ∀ (K K' : Type u) [NontriviallyNormedField K] [NontriviallyNormedField K']
    [NormedAlgebra K K'] [FiniteDimensional K K'],
    IsHenselianValuedField K → IsHenselianValuedField K' →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)), IsLocallySeparatedLocallyFiniteType K X →
      let φ : RingPoints K X K →
          RingPoints K' (baseChange (Spec.algebraMap K K') X) K' := fun x =>
        (baseChangeRingPointsEquiv K K' K' X).symm
          (RingPoints.changeRing (Algebra.ofId K K') x)
      @Topology.IsEmbedding _ _ (etaleChartTopology K X)
        (etaleChartTopology K' (baseChange (Spec.algebraMap K K') X)) φ

end Langlands.AlgebraicGeometry.AlgebraicSpace
