import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianSpacePointTopologyStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange

/-!
# Rational points over an extension of henselian valued fields

Conrad's Proposition 5.11(3): for an extension `K'/K` of henselian valued fields and a
quasi-separated algebraic space locally of finite type over `K` that is covered by
separated Zariski-open subspaces, the natural map `X(K) → X_{K'}(K')` is a topological
embedding for the étale-chart topologies, and a closed embedding when `K` is closed in
`K'`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable (K : Type u) [Field K]

/-- An algebraic space over `Spec K` is covered by separated Zariski-open subspaces: every
field-valued point `Spec L → X` factors through an open immersion `U ⟶ X` from a
separated algebraic space `U`. -/
def IsCoveredBySeparatedOpenSubspaces (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] (x : RingPoints K X L),
    ∃ (U : AlgebraicSpace (Spec (CommRingCat.of K))) (j : U ⟶ X),
      IsOpenImmersion (hom j) ∧ IsSeparated U ∧ x ∈ Set.range (RingPoints.map (A := L) j)

/-- Conrad's Proposition 5.11(3) (printed p.18): let `K'/K` be an extension of henselian
valued fields, the norm of `K'` restricting to that of `K`. For every quasi-separated
algebraic space `X` locally of finite type over `Spec K` that is covered by separated
Zariski-open subspaces, the map `X(K) → X_{K'}(K')`, viewing a rational point as a
`K'`-valued point and then as a rational point of the base change to `Spec K'`, is a
topological embedding for the étale-chart topologies over `K` and over `K'`. It is a
closed embedding when `K` is closed in `K'`. -/
def HenselianExtensionPointEmbeddingStatement : Prop :=
  ∀ (K K' : Type u) [NontriviallyNormedField K] [NontriviallyNormedField K']
    [NormedAlgebra K K'], IsHenselianValuedField K → IsHenselianValuedField K' →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)), IsQuasiSeparatedLocallyFiniteType K X →
      IsCoveredBySeparatedOpenSubspaces K X →
      let φ : RingPoints K X K →
          RingPoints K' (baseChange (Spec.algebraMap K K') X) K' := fun x =>
        (baseChangeRingPointsEquiv K K' K' X).symm
          (RingPoints.changeRing (Algebra.ofId K K') x)
      @Topology.IsEmbedding _ _ (etaleChartTopology K X)
          (etaleChartTopology K' (baseChange (Spec.algebraMap K K') X)) φ ∧
        (IsClosed (Set.range (algebraMap K K')) →
          @Topology.IsClosedEmbedding _ _ (etaleChartTopology K X)
            (etaleChartTopology K' (baseChange (Spec.algebraMap K K') X)) φ)

end Langlands.AlgebraicGeometry.AlgebraicSpace
