import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Upper building data from the supplied unramified apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}

private instance apartmentInputExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- The upper building datum uses exactly the supplied upper apartment,
centralizer and V6 compatibility. Reductivity ascends from the base group. -/
def buildingDataOfApartment (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) :
    letI := mono_of_isMaximalSplitTorus hiT
    ∀ (D : KPApartmentData
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (valuation F)))
      (C : CentralizerDatum
        (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      IntegerValuation.IsOmegaCompatible (valuation F) D C →
        BuildingData F (baseChanged F (inertiaFixedField F) G) := by
  letI := mono_of_isMaximalSplitTorus hiT
  intro D C hDC
  exact
    { isConnectedReductive := hG.baseChange_of_algebraicExtension
      S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T
      i := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT
      isMaximalSplitTorus := hiT
      apartment := D
      centralizer := C
      isOmegaCompatible := hDC }

end Langlands.Geometry.Building.MaximalUnramified
