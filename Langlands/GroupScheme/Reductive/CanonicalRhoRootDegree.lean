import Langlands.GroupScheme.Reductive.CanonicalRhoCovariance
import Langlands.GroupScheme.Reductive.RankOneCovariantCutoff

/-! # Actual simple-root curve bounds for the full canonical induced space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Polynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance canonicalRhoRootDegreeIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual polynomial coordinate along the fixed linked negative
simple-root curve through the supplied rational point. -/
def linkedNegativeSimpleCurvePolynomial (r : p.base.support)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    AffineCoordinates.algebra G →ₐ[k] k[X] :=
  RankOneCovariantCutoff.curvePolynomial G
    (RankOneCovariantCutoff.negativeCurve G (p.linkedRootParametrization r).negative g)

variable [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

/-- Every member of the full canonical negative-rho induced space has degree
at most m along each fixed linked negative simple-root curve, at every rational
translate. Both rank-one covariance hypotheses follow from actual membership. -/
theorem natDegree_linkedNegativeSimpleCurvePolynomial_le [Infinite k]
    (m : ℕ) {f : AffineCoordinates.algebra G}
    (hf : f ∈ p.canonicalRhoCovariantSubspace hspan m)
    (r : p.base.support)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (p.linkedNegativeSimpleCurvePolynomial r g f).natDegree ≤ m := by
  exact RankOneCovariantCutoff.natDegree_negativeCurve_le G
    p.inclusion (p.rootDatum.coroot r)
    (p.linkedRootParametrization r).positive (p.linkedRootParametrization r).negative
    (p.linkedRootParametrization r).relation f m
    (fun Z a h => p.canonicalRhoCovariantSubspace_left_linkedPositive hspan m hf
      r (p.base.isPos_of_mem_support r.property) Z a h)
    (fun Z z h => p.canonicalRhoCovariantSubspace_left_simpleCoroot hspan m hf r Z z h) g

end Langlands.GroupScheme.SplitPinning
