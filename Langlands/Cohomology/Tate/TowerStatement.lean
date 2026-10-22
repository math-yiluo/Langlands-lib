import Langlands.Cohomology.Tate.TransferDefinitions
import Langlands.Cohomology.Tate.TowerReindex

universe u

open CategoryTheory

namespace Langlands.Tate

/-- Transitivity through a subgroup tower, with the actual change-of-group identification. -/
def TowerLaws : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G] [Fintype G]
    (K H : Subgroup G) (h : K ≤ H)
    [Fintype K] [Fintype H] [Fintype (K.subgroupOf H)]
    [Fintype (G ⧸ K)] [Fintype (G ⧸ H)] [Fintype (H ⧸ K.subgroupOf H)]
    (A : Rep R G) (n : ℤ),
    (∀ x : tateCohomology A n,
      (towerReindex h A n).hom (restriction K A n x) =
        restriction (K.subgroupOf H) (Rep.res H.subtype A) n (restriction H A n x)) ∧
    (∀ x : tateCohomology (Rep.res K.subtype A) n,
      corestriction K A n x =
        corestriction H A n (corestriction (K.subgroupOf H) (Rep.res H.subtype A) n
          ((towerReindex h A n).hom x)))

end Langlands.Tate
