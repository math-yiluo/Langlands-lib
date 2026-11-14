import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.Geometry.Building.UnramifiedZeroIndependenceProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof

/-! # Zero data compatible with a supplied unramified apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (B : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)

namespace UnramifiedZeroDatum

/-- Extend the original apartment torus to a maximal torus. Quasi-splitness
over the actual maximal unramified field identifies it with the whole
centralizer. Retain the given simply connected derived cover. -/
def apartmentCompatibleData :
    {E' : UnramifiedZeroDatum F G // (torusCentralizer B.i).IsRepresentedBy E'.i} := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let hT := exists_maximalTorus_extension_of_finiteType G B.i
    B.isMaximalSplitTorus.1.1.isTorus B.isMaximalSplitTorus.1.2
  let T := hT.choose
  let j := hT.choose_spec.choose
  have hj : IsMaximalTorus j := hT.choose_spec.choose_spec.1
  let f := hT.choose_spec.choose_spec.2.choose
  have hf : f ≫ j = B.i := hT.choose_spec.choose_spec.2.choose_spec
  let : IsClosedImmersion j.hom.hom.left := hj.2.1
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine T.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let hL := exists_finiteGaloisSplittingField_inside (SeparableClosure F) T.toGrp hj.1
  let L := hL.choose
  let E' : UnramifiedZeroDatum F G := {
    T := T
    isAffine := inferInstance
    i := j
    isMaximallySplitMaximalTorus := ⟨hj, B.S, B.i, f, B.isMaximalSplitTorus, hf⟩
    L := L
    finiteDimensional := hL.choose_spec.1
    isGalois := hL.choose_spec.2.1
    isSplitTorus := hL.choose_spec.2.2
    D := E.D
    C := E.C
    d := E.d
    π := E.π
    isSimplyConnectedDerivedCover := E.isSimplyConnectedDerivedCover }
  refine ⟨E', ?_⟩
  exact quasiSplitMaximalTorusCentralizer _ G
    (unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit
      F G B.isConnectedReductive) T B.S j B.i f hj B.isMaximalSplitTorus hf

/-- Zero data whose maximal torus represents the centralizer of the original
apartment torus, with the original derived cover. -/
def withApartmentTorus : UnramifiedZeroDatum F G :=
  (apartmentCompatibleData B E).val

/-- The new torus represents the whole centralizer on every test scheme. -/
theorem withApartmentTorus_isRepresentedBy :
    (torusCentralizer B.i).IsRepresentedBy (withApartmentTorus B E).i :=
  (apartmentCompatibleData B E).property

/-- The original derived subgroup is retained. -/
@[simp]
theorem withApartmentTorus_D : (withApartmentTorus B E).D = E.D := rfl

/-- The original simply connected cover is retained. -/
@[simp]
theorem withApartmentTorus_C : (withApartmentTorus B E).C = E.C := rfl

/-- Replacing the torus choices does not change the actual cover image. -/
@[simp]
theorem withApartmentTorus_simplyConnectedImage :
    (withApartmentTorus B E).simplyConnectedImage = E.simplyConnectedImage := rfl

/-- The published independence theorem identifies the actual zero subgroups. -/
@[simp]
theorem withApartmentTorus_zeroPoints :
    (withApartmentTorus B E).zeroPoints = E.zeroPoints :=
  unramifiedZeroPointsIndependence F G _ E

/-- The original and compatible zero groups are identified point by point. -/
def withApartmentTorusZeroEquiv :
    ↥(withApartmentTorus B E).zeroPoints ≃* E.zeroPoints :=
  MulEquiv.subgroupCongr (withApartmentTorus_zeroPoints B E)

@[simp]
theorem coe_withApartmentTorusZeroEquiv
    (g : ↥(withApartmentTorus B E).zeroPoints) :
    (withApartmentTorusZeroEquiv B E g : rationalPoints G) = g := rfl

end UnramifiedZeroDatum

end Langlands.Geometry.Building
