import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof

/-! # Actual unramified building data on a prescribed maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}

/-- Every connected reductive group over the actual inertia fixed field is quasi-split. -/
theorem isQuasiSplit (hH : IsConnectedReductive H) : IsQuasiSplit H :=
  unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit F H hH

variable [IsAffineHom H.X.hom]
    (hH : IsConnectedReductive H)
    {S : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    (i : S.toGrp ⟶ H) (hi : IsMaximalSplitTorus i)

/-- Choose actual compatible building data whose torus and inclusion are the prescribed ones. -/
def prescribedBuildingData : BuildingData F H := by
  letI := mono_of_isMaximalSplitTorus hi
  have h := quasiSplitIntegerApartmentExistence
    (inertiaFixedField F) (valuation F) (valuation_surjective F)
    (valuationSubring_isHenselian F) H (isQuasiSplit F hH) S i hi
  exact
    { isConnectedReductive := hH
      S := S
      i := i
      isMaximalSplitTorus := hi
      apartment := Classical.choose h
      centralizer := Classical.choose (Classical.choose_spec h)
      isOmegaCompatible := Classical.choose_spec (Classical.choose_spec h) }

@[simp] theorem prescribedBuildingData_S :
    (prescribedBuildingData F hH i hi).S = S := rfl

@[simp] theorem prescribedBuildingData_i :
    (prescribedBuildingData F hH i hi).i = i := rfl

end Langlands.Geometry.Building.MaximalUnramified
