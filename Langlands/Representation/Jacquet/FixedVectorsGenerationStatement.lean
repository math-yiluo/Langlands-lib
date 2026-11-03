import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.Smooth.Definitions

/-!
# Algebraic fixed-vector generation of actual Jacquet coinvariants

The algebraic core of the lemma preceding Howe's theorem in Renard VI.6.3.
The normalizer and factorization hypotheses remain explicit.
-/

set_option autoImplicit false

namespace Langlands.Jacquet

universe uR uG uV

/-- If `K₀` normalizes `K`, every element factors through `M`, `N`, and
`K₀`, and `K`-fixed vectors generate the ambient representation, then
`K ∩ M`-fixed vectors generate its actual unnormalized `N`-coinvariants. -/
def FixedVectorsGenerationStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (N M K K₀ : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N),
    K₀ ≤ Subgroup.normalizer K →
    (∀ g : G, ∃ m ∈ M, ∃ n ∈ N, ∃ k ∈ K₀, g = m * n * k) →
    (∀ T : Subrepresentation ρ, fixedVectors ρ K ≤ T.toSubmodule → T = ⊤) →
    ∀ S : Subrepresentation (action ρ N M hMN),
      fixedVectors (action ρ N M hMN) (K.comap M.subtype) ≤ S.toSubmodule →
      S = ⊤

end Langlands.Jacquet
