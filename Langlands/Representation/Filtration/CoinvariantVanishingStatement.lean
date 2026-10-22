import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Jacquet.Coinvariants

namespace Langlands.Jacquet

universe uR uG uV

/-- A finite actual representation filtration with vanishing subgroup
coinvariants in every graded quotient has vanishing ambient coinvariants. -/
def CoinvariantFiltrationVanishingTheorem : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G]
    (A : Rep.{uV} R G) (m : ℕ) (s : ObjectRepFiltration A m) (N : Subgroup G),
    (∀ i, Subsingleton (Coinvariants (s.gradedRepresentation i).ρ N)) →
      Subsingleton (Coinvariants A.ρ N)

end Langlands.Jacquet
