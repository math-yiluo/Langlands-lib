import Langlands.Geometry.Building.ValuedSU3CoordinateAssembly

/-! # Specialization of supplied rank-one coordinates to the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : MaximalUnramified.BuildingData F H) (hZ : IsTorus B.centralizer.Z)
  {b : characterLattice B.S}

private instance splitTorusAffine : IsAffine B.S.toGrp.X.left := by
  letI : IsAffineHom B.S.toGrp.X.hom := B.isMaximalSplitTorus.isSplitSubtorus.1.isAffineHom
  exact isAffine_of_isAffineHom B.S.toGrp.X.hom

private instance centralizerAffine : IsAffine B.centralizer.Z.X.left := by
  letI : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  letI : IsClosedImmersion B.centralizer.j.hom.hom.left := B.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom B.centralizer.j.hom.hom.left

/-- Supplied coherent SL2 coordinates with a normalizing Weyl image yield the exact
published valued record over the maximal unramified field. -/
def ValuedSL2RootCoordinates.ofAlgebraic
    (C : AlgebraicSL2RootCoordinates (Z := B.centralizerTorus hZ)
      B.i B.centralizer.j B.centralizer.s b)
    (hb : b ∈ relativeRoots B.i)
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints B.i) :
    ValuedSL2RootCoordinates B hZ b := by
  have hdepth := C.coordinateOrigin_depths B.centralizer hZ B.apartment
    B.isOmegaCompatible B.isConnectedReductive B.isMaximalSplitTorus hb hn
    (IntegerValuation.isNormCalibrated_henselianSeparableAddValuation
      (MaximalUnramified.valuationSubring_isHenselian F) C.extension)
  exact {
    extension := C.extension
    positive := C.positive
    negative := C.negative
    rho := C.rho
    rho_upper := C.rho_upper
    rho_lower := C.rho_lower
    coroot := C.coroot
    coroot_points := C.coroot_points
    origin := C.coordinateOrigin B.centralizer hZ B.apartment hn
    depth_positive := hdepth.1
    depth_negative := hdepth.2 }

/-- Supplied coherent SU3 coordinates with a normalizing Weyl image yield all four
formulas in the published valued record over the maximal unramified field. -/
def ValuedSU3RootCoordinates.ofAlgebraic
    (C : AlgebraicSU3RootCoordinates (Z := B.centralizerTorus hZ)
      B.i B.centralizer.j B.centralizer.s b)
    (hb : b ∈ relativeRoots B.i) (h2b : 2 • b ∈ relativeRoots B.i)
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints B.i) :
    ValuedSU3RootCoordinates B hZ b := by
  have hw := IntegerValuation.isNormCalibrated_henselianSeparableAddValuation
    (MaximalUnramified.valuationSubring_isHenselian F) C.extension
  have hbar := SU3Root.henselianSeparableAddValuation_quadratic_bar
    (UnramifiedClosure F) C.base C.extension (MaximalUnramified.valuation F)
    (MaximalUnramified.valuationSubring_isHenselian F)
  have hdepth := C.coordinateOrigin_depths B.centralizer hZ B.apartment
    B.isOmegaCompatible B.isConnectedReductive B.isMaximalSplitTorus hb hn hw hbar
  have hdouble := C.coordinateOrigin_double_depths B.centralizer hZ B.apartment
    B.isOmegaCompatible B.isConnectedReductive B.isMaximalSplitTorus hb h2b hn hw hbar
  exact {
    base := C.base
    extension := C.extension
    positive := C.positive
    negative := C.negative
    rho := C.rho
    rho_upper := C.rho_upper
    rho_lower := C.rho_lower
    coroot := C.coroot
    coroot_points := C.coroot_points
    origin := C.coordinateOrigin B.centralizer hZ B.apartment hn
    depth_positive := hdepth.1
    depth_negative := hdepth.2
    depth_double_positive := hdouble.1
    depth_double_negative := hdouble.2 }

end Langlands.Geometry.Building
