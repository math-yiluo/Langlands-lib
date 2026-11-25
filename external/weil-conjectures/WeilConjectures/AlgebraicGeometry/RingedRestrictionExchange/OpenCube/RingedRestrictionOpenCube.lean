/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement

/-! # Shared coefficient presentations for open restriction cubes

## References

* Stacks 09A5, 03CB and 00XZ
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- An open restriction of the square, with shared coefficients at all eight vertices.
Each face is Cartesian and each coefficient comparison is coherent with its two
composite inverse-image maps. Thus the fields describe presentations of the actual
inverse-image rings, rather than extra hypotheses on schemes or complexes. -/
structure OpenCube (r : StrictTowerRingedSquare sq) {U : Scheme.{u}} (j : U ⟶ Y) where
  XU : Scheme.{u}
  YU' : Scheme.{u}
  XU' : Scheme.{u}
  jX : XU ⟶ X
  jY' : YU' ⟶ Y'
  jX' : XU' ⟶ X'
  fU : XU ⟶ U
  gU : YU' ⟶ U
  fU' : XU' ⟶ YU'
  gU' : XU' ⟶ XU
  localSquare : ChosenCartesianSquare gU' fU' fU gU
  sourceSquare : ChosenCartesianSquare jX fU f j
  targetSquare : ChosenCartesianSquare jX' fU' f' jY'
  baseSquare : ChosenCartesianSquare jY' gU g j
  upperSquare : ChosenCartesianSquare jX' gU' g' jX
  localRings : StrictTowerRingedSquare localSquare
  cj : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj r.RY ≅ localRings.RY
  cjX : (proEtaleSheafInverseImage jX CommRingCat.{u + 1}).obj r.RX ≅ localRings.RX
  cjY' : (proEtaleSheafInverseImage jY' CommRingCat.{u + 1}).obj r.RY' ≅ localRings.RY'
  cjX' : (proEtaleSheafInverseImage jX' CommRingCat.{u + 1}).obj r.RX' ≅ localRings.RX'
  sourceCoherent : HEq
    (proEtaleRingCompositeCoefficients jX f r.RY r.RX localRings.RX r.cf cjX)
    (proEtaleRingCompositeCoefficients fU j r.RY localRings.RY localRings.RX cj localRings.cf)
  targetCoherent : HEq
    (proEtaleRingCompositeCoefficients jX' f' r.RY' r.RX' localRings.RX' r.cf' cjX')
    (proEtaleRingCompositeCoefficients fU' jY' r.RY' localRings.RY' localRings.RX'
      cjY' localRings.cf')
  baseCoherent : HEq
    (proEtaleRingCompositeCoefficients jY' g r.RY r.RY' localRings.RY' r.cg cjY')
    (proEtaleRingCompositeCoefficients gU j r.RY localRings.RY localRings.RY' cj localRings.cg)
  upperCoherent : HEq
    (proEtaleRingCompositeCoefficients jX' g' r.RX r.RX' localRings.RX' r.cg' cjX')
    (proEtaleRingCompositeCoefficients gU' jX r.RX localRings.RX localRings.RX'
      cjX localRings.cg')

variable {U : Scheme.{u}} {j : U ⟶ Y}

/-- The p/open face, with shared coefficient objects. -/
def OpenCube.sourceFace {r : StrictTowerRingedSquare sq} (C : OpenCube r j) :
    StrictTowerRingedSquare C.sourceSquare where
  RY := r.RY
  RX := r.RX
  RY' := C.localRings.RY
  RX' := C.localRings.RX
  cf := r.cf
  cg := C.cj
  cg' := C.cjX
  cf' := C.localRings.cf
  coherent := C.sourceCoherent

/-- The p'/open face, with shared coefficient objects. -/
def OpenCube.targetFace {r : StrictTowerRingedSquare sq} (C : OpenCube r j) :
    StrictTowerRingedSquare C.targetSquare where
  RY := r.RY'
  RX := r.RX'
  RY' := C.localRings.RY'
  RX' := C.localRings.RX'
  cf := r.cf'
  cg := C.cjY'
  cg' := C.cjX'
  cf' := C.localRings.cf'
  coherent := C.targetCoherent

/-- The h/open pullback-composition face. -/
def OpenCube.baseFace {r : StrictTowerRingedSquare sq} (C : OpenCube r j) :
    StrictTowerRingedSquare C.baseSquare where
  RY := r.RY
  RX := r.RY'
  RY' := C.localRings.RY
  RX' := C.localRings.RY'
  cf := r.cg
  cg := C.cj
  cg' := C.cjY'
  cf' := C.localRings.cg
  coherent := C.baseCoherent

/-- The h'/open pullback-composition face. -/
def OpenCube.upperFace {r : StrictTowerRingedSquare sq} (C : OpenCube r j) :
    StrictTowerRingedSquare C.upperSquare where
  RY := r.RX
  RX := r.RX'
  RY' := C.localRings.RX
  RX' := C.localRings.RX'
  cf := r.cg'
  cg := C.cjX
  cg' := C.cjX'
  cf' := C.localRings.cg'
  coherent := C.upperCoherent

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
