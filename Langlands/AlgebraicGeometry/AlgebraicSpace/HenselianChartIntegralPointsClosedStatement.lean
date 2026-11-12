import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsStatement

/-!
# Integral points of one affine étale chart have closed image

An intermediate statement for the closedness part of Conrad's Corollary 5.7. Let `O` be
the closed unit ball of a nontrivially normed field `K`, assumed to be a henselian local
ring, and let `X` be a separated algebraic space locally of finite type over `Spec O`.
For one affine scheme `U` with an étale map `f : U → X`, the `O`-points of `U`, viewed as
rational points of the generic fibre `X_K`, form a closed subset for the étale-chart
topology.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Closed image of the integral points of one affine étale chart: let `K` be a
nontrivially normed field whose closed unit ball is a subring `O`, and assume `O` is
henselian. Let `X` be a separated algebraic space locally of finite type over `Spec O`, and
let `f : U → X` be an étale morphism from an affine scheme `U` over `Spec O`. Then the set
of images in `X_K(K)` of the `O`-points of `U`, each mapped to an `O`-point of `X` by `f`,
viewed as a `K`-point and then as a rational point of the base change to `Spec K`, is closed
for the étale-chart topology. -/
def HenselianChartIntegralPointsClosedStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] (O : Subring K), (∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1) →
    HenselianLocalRing O →
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of O)), IsSeparated X →
      LocallyOfFiniteTypeOverBase X →
      ∀ (U : Over (Spec (CommRingCat.of O))) (f : (schemeToSpace _).obj U ⟶ X),
        IsAffine U.left → IsEtale (hom f) →
          IsClosed[etaleChartTopology K (baseChange (Spec.algebraMap O K) X)]
            (Set.range fun u : RingPoint O U O =>
              (baseChangeRingPointsEquiv O K K X).symm
                (RingPoints.changeRing (Algebra.ofId O K)
                  (RingPoints.map f ((schemeRingPointsEquiv O U O).symm u))))

end Langlands.AlgebraicGeometry.AlgebraicSpace
