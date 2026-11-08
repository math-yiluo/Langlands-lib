import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsStatement

/-!
# Closedness of integral points over locally compact fields

Conrad's Corollary 5.7, closedness, in the case of a locally compact field. Let `O` be the
valuation ring of a locally compact nontrivially normed non-archimedean field `K`. For a
separated algebraic space `X` over `Spec O`, the map `X(O) → X_K(K)` is injective, and its image
is closed when `X` is of finite type.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Corollary 5.7 (printed p.16), closedness over a locally compact field: let `K` be
a locally compact nontrivially normed field whose closed unit ball is a subring `O`, and assume
`O` is henselian. For every separated algebraic space `X` over `Spec O`, the map
`X(O) → X_K(K)`, viewing an `O`-point as a `K`-point and then as a rational point of the base
change to `Spec K`, is injective. If `X` is moreover of finite type over `O`, its image is closed
for the étale-chart topology. -/
def HenselianIntegralPointsClosedOfLocallyCompactStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (O : Subring K), (∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) →
    HenselianLocalRing O → LocallyCompactSpace K →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of O)), IsSeparated X →
      let ι : RingPoints O X O → RingPoints K (baseChange (Spec.algebraMap O K) X) K :=
        fun x => (baseChangeRingPointsEquiv O K K X).symm
          (RingPoints.changeRing (Algebra.ofId O K) x)
      Function.Injective ι ∧
        (FiniteTypeOverRing O X →
          IsClosed[etaleChartTopology K (baseChange (Spec.algebraMap O K) X)] (Set.range ι))

end Langlands.AlgebraicGeometry.AlgebraicSpace
