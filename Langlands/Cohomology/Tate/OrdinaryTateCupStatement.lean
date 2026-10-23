import Langlands.Cohomology.Tate.OrdinaryCupDefinitions
import Langlands.Cohomology.Tate.OrdinaryTateComparison
import Langlands.Cohomology.Tate.CupDefinitions

universe u

open CategoryTheory

namespace Langlands.Tate

/-- The actual ordinary cup agrees with the Tate cup under the canonical comparison. -/
def OrdinaryTateCupLaws : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G] [Fintype G]
    (A B C : Rep.{u} R G) (φ : Pairing A B C)
    (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology B q),
    (tateDegreeIso C (show ((p + q : ℕ) : ℤ) = (p : ℤ) + q by omega)).hom
      (ordinaryToTate C (p + q) (ordinaryCup φ p q a b)) =
      cup φ p q (ordinaryToTate A p a) (ordinaryToTate B q b)

end Langlands.Tate
