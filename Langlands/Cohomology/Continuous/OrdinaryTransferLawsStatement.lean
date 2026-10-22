import Langlands.Cohomology.Tate.CohomologyTransfer
import Langlands.Cohomology.Tate.TowerReindex

universe u

open CategoryTheory

namespace Langlands.Continuous

/-- The actual ordinary restriction followed by corestriction multiplies by the index. -/
def OrdinaryCorestrictionIndex : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)] (A : Rep.{u} k G) (q : ℕ),
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) q ≫
        Langlands.Tate.ordinaryCohomologyCorestriction H A q =
      H.index • 𝟙 (groupCohomology A q)

/-- Actual ordinary corestriction is transitive through the explicit subgroup coordinates. -/
def OrdinaryCorestrictionTower : Prop :=
  ∀ (k G : Type u) [CommRing k] [Group G] [Fintype G]
    (K H : Subgroup G) (h : K ≤ H)
    [Fintype K] [Fintype H] [Fintype (K.subgroupOf H)]
    [Fintype (G ⧸ K)] [Fintype (G ⧸ H)] [Fintype (H ⧸ K.subgroupOf H)]
    (A : Rep.{u} k G) (q : ℕ),
    Langlands.Tate.ordinaryCohomologyCorestriction K A q =
      groupCohomology.map (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
          (Langlands.Tate.towerCoefficientIso h A).hom q ≫
        Langlands.Tate.ordinaryCohomologyCorestriction (K.subgroupOf H)
          (Rep.res H.subtype A) q ≫
        Langlands.Tate.ordinaryCohomologyCorestriction H A q

/-- The finite ordinary index and tower laws needed for continuous transfer. -/
def OrdinaryTransferLaws : Prop :=
  OrdinaryCorestrictionIndex.{u} ∧ OrdinaryCorestrictionTower.{u}

end Langlands.Continuous
