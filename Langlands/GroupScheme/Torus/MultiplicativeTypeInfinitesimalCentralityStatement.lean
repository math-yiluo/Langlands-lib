import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Rational.Characters

/-! # Statement: centrality of homomorphisms from groups of multiplicative type spreads from nilpotent thickenings -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Centrality spreads from a nilpotent thickening** (SGA 3, IX, Corollaire 3.9). Let `S` be
a scheme and `i : S₀ ⟶ S` a closed immersion whose ideal sheaf is locally nilpotent: every
point of `S` lies in an affine open `U` on which the ideal `ker(Γ(S, U) → Γ(S₀, i⁻¹U))` is
nilpotent. Let `u : G ⟶ H` be a homomorphism of `S`-groups with `G` of multiplicative type and
`H` locally of finite presentation over `S`. If the base change `u₀ : G_{S₀} ⟶ H_{S₀}` is
central, then `u` is central. -/
def MultiplicativeTypeInfinitesimalCentralityStatement : Prop :=
  ∀ (S S₀ : Scheme.{u}) (i : S₀ ⟶ S) [IsClosedImmersion i],
    (∀ x : S, ∃ U : S.affineOpens, x ∈ (U : S.Opens) ∧ IsNilpotent (i.ker.ideal U)) →
    ∀ (G H : GroupScheme S) [LocallyOfFinitePresentation H.X.hom],
      RelativeMultiplicativeType.IsMultiplicativeType G →
      ∀ u : G ⟶ H, IsCentral ((GroupScheme.baseChange i).map u) → IsCentral u

end Langlands.GroupScheme
