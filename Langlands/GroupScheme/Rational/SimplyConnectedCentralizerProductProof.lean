import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductStatement
import Langlands.GroupScheme.Rational.DerivedCoverWeylLift
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Proof: `G(k) = G(k)^♮ · Z_G(S)(k)` (KP Fact 2.6.22, minimal Levi case) -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **KP Fact 2.6.22 for the minimal Levi subgroup**, over an arbitrary field. Every rational
point of a connected reductive group is the image of a rational point of the simply connected
cover of its derived subgroup times a rational point of the centralizer of a maximal split
torus. -/
theorem simplyConnectedCentralizerProduct :
    SimplyConnectedCentralizerProductStatement.{u} := by
  intro k _ S G Z C D i j d π hcover hi hj g
  have hG := hcover.isConnectedReductive
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let : Smooth G.X.hom := hG.smooth
  have hE : RelativeRoot.HasOppositeFactorPairs i := fun a ha x hx hx1 =>
    (rootRankOneFactorization k G hG S i hi a ha x hx hx1).1.exists
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  exact exists_derivedCover_mul_centralizer_of_oppositeFactorPairs i j hcover hi hj hE
    (relativeRootSystem k G hG S i hi) ν hν (rationalBruhat k G hG S i hi ν hν) g

end Langlands.GroupScheme
