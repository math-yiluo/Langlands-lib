import Langlands.GroupScheme.Rational.RankOneWeylImage
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeWeylFaithfulness
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # The actual reductive relative Weyl quotient in rank at most one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual reductive relative Weyl quotient in semisimple rank at most one
embeds in the two possible global signs of its root-span action. -/
def IsConnectedReductive.rankOneRelativeWeylQuotientSignEmbedding
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) :
    relativeWeylGroup i ↪ Bool := by
  letI := hG.isAffineHom
  letI := hG.smooth
  letI := hi.isSplitSubtorus.mono
  let e := MonoidHom.ofInjective (hi.1.1.relativeWeylAction_injective_of_span i
    (relativeRootsRestrictedCharactersSpan k G hG T i hi))
  exact e.toEquiv.toEmbedding.trans (hi.1.1.rankOneRelativeWeylSignEmbedding i hdep)

/-- Pairwise integral dependence of the actual roots bounds the order of the
actual reductive relative Weyl quotient by two. -/
theorem IsConnectedReductive.card_relativeWeylGroup_le_two_of_rankOne
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) :
    Nat.card (relativeWeylGroup i) ≤ 2 := by
  simpa using Nat.card_le_card_of_injective
    (hG.rankOneRelativeWeylQuotientSignEmbedding i hi hdep)
    (hG.rankOneRelativeWeylQuotientSignEmbedding i hi hdep).injective

/-- The sign encoding for the split maximal-torus convention. -/
def IsConnectedReductive.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) :
    relativeWeylGroup i ↪ Bool :=
  hG.rankOneRelativeWeylQuotientSignEmbedding i (hi.isMaximalSplitTorus hT) hdep

/-- The order bound for a split maximal torus in a connected reductive group. -/
theorem IsConnectedReductive.card_relativeWeylGroup_le_two_of_rankOne_of_isMaximalTorus
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) :
    Nat.card (relativeWeylGroup i) ≤ 2 :=
  hG.card_relativeWeylGroup_le_two_of_rankOne i (hi.isMaximalSplitTorus hT) hdep

end Langlands.GroupScheme
