import Langlands.Cohomology.Tate.TransferDefinitions
import Langlands.Cohomology.Tate.CohomologyTransfer

universe u

open CategoryTheory

namespace Langlands.Tate

/-- Tate subgroup maps agree with ordinary cohomology and homology maps away from the splice. -/
def OrdinaryComparisons : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]
    (A : Rep R G) (n : ℕ) [NeZero n],
    (ModuleCat.ofHom (restriction H A n) =
      ((TateCohomology.isoGroupCohomology n).app A).hom ≫
        groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n ≫
          ((TateCohomology.isoGroupCohomology n).app (Rep.res H.subtype A)).inv) ∧
    (ModuleCat.ofHom (corestriction H A n) =
      ((TateCohomology.isoGroupCohomology n).app (Rep.res H.subtype A)).hom ≫
        ordinaryCohomologyCorestriction H A n ≫
          ((TateCohomology.isoGroupCohomology n).app A).inv) ∧
    (ModuleCat.ofHom (corestriction H A (-(n + 1 : ℤ))) =
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app
        (Rep.res H.subtype A)).hom ≫
        groupHomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n ≫
          ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).inv) ∧
    (ModuleCat.ofHom (restriction H A (-(n + 1 : ℤ))) =
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).hom ≫
        ordinaryHomologyTransfer H A n ≫
          ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app
            (Rep.res H.subtype A)).inv)

end Langlands.Tate
