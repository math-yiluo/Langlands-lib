import Langlands.GroupScheme.IntegralModel.CongruenceCell
import Langlands.GroupScheme.Dynamic.BaseTripleCell

/-! # Integral three-factor cells from actual dynamic representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IntegralModel.IntegralTripleCellData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G V Z U : GroupScheme (Spec (CommRingCat.of K))}
    {iV : V ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (M : IntegralModel R K G) [Smooth M.group.X.hom]

/-- Construct the supplied integral triple-cell data from integral models whose
actual maps represent the three dynamic subgroups of an integral cocharacter. -/
def ofDynamic
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ M.group)
    (negative : IntegralModel R K V)
    (middle : IntegralModel R K Z)
    (positive : IntegralModel R K U)
    (negativeMap : negative.Hom M iV)
    (middleMap : middle.Hom M iZ)
    (positiveMap : positive.Hom M iU)
    (hV : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of R)) (-1)) ≫ χ)).IsRepresentedBy
        negativeMap.hom)
    (hZ : (Dynamic.centralizer χ).IsRepresentedBy middleMap.hom)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy positiveMap.hom) :
    IntegralTripleCellData M V Z U iV iZ iU where
  negative := negative
  middle := middle
  positive := positive
  negativeMap := negativeMap
  middleMap := middleMap
  positiveMap := positiveMap
  openCell := Dynamic.isOpenImmersion_tripleCellMultiplication_overBase χ hV hZ hU

end IntegralModel.IntegralTripleCellData
end Langlands.GroupScheme
