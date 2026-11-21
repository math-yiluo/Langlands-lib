import Langlands.GroupScheme.Rational.DominantHighestWeight
import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.HomogeneousCharacterLineBundle

/-! # Statement: nonvanishing of the spaces `E(λ)` of Borel-equivariant functions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 22.27(a), in the 2022 corrected reprint. Let `p` be a split pinning of
a connected reductive group `G` over a field `k`, with split maximal torus `T`, and let
`i : B' ⟶ G` be the opposite Borel subgroup `B⁻ = P(ν)` attached to a cocharacter `ν` that is
negative on the simple roots of `p`. For a character `χ : B' ⟶ 𝔾_m` with restriction `λ` to
`T`, the space `E(λ)` of functions `f ∈ O(G)` with `f(gb) = f(g) χ(b)⁻¹` for all points `g`
of `G` and `b` of `B'` is nonzero if and only if `λ` is dominant. -/
def SplitBorelInducedNonvanishingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (ν : cocharacterLattice p.torus),
    (∀ a : p.base.support, latticePairing p.torus (p.rootDatum.root a) ν < 0) →
    ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (i : B' ⟶ G), IsClosedSubgroup i →
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ p.inclusion)).IsRepresentedBy i →
    ∀ (t : p.torus.toGrp ⟶ B'), t ≫ i = p.inclusion →
    ∀ χ : rationalCharacters B',
      (∃ f : Γ(G.X.left, ⊤), f ≠ 0 ∧
        HomogeneousQuotientFromEmbedding.IsRightCharacterCovariant i (-χ) f) ↔
      p.IsDominantWeight (rationalCharacters.equivCharacterLattice p.torus (characterRestrict t χ))

end Langlands.GroupScheme
