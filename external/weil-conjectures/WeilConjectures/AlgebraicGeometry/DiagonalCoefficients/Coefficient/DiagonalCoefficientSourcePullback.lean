/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints

/-! # Canonical pullback of diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-source-pullback).

## Main definitions

- `baseP`, `baseW`: the actual projective-line base-change maps.
- `SourcePullback`: ordinary source, coefficient-unit and positive-line data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The projective-line map in the actual geometric base-change square.
Source: blueprint clause 3 (blueprint: def-sfb-diagonal-coefficient-source-pullback). -/
def baseP {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) : ProjectiveLine Y' ⟶ ProjectiveLine Y :=
  ProjectiveSpace.map (ULift.{u} (Fin 2)) g

/-- The two-factor base-change map, using the chosen fibre products.
Source: blueprint clause 3 (blueprint: def-sfb-diagonal-coefficient-source-pullback). -/
def baseW {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) : diagonalSurface Y' ⟶ diagonalSurface Y :=
  pullback.map (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y')
    (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) (baseP g) (baseP g) g
    (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm
    (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm

/-- The three commutative squares of the fixed geometric base change.
Source: blueprint base-change geometry
(blueprint: def-sfb-diagonal-coefficient-source-pullback). -/
structure BaseSquares {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) where
  diagonal_square : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y
  first_square : pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y') ≫ baseP g =
    baseW g ≫ pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
  second_square : pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y') ≫ baseP g =
    baseW g ≫ pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)

/-- The two coefficient-unit and two positive-line endpoints, before any
source or derived equation is imposed. Source: blueprint base-change endpoints
(blueprint: def-sfb-diagonal-coefficient-source-pullback). -/
structure PullbackEndpoints
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L : ∀ X : Scheme.{u}, Modules R X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X) where
  cY : UnitPullEndpoint R g
  cP : UnitPullEndpoint R (baseP g)
  lineP : PullEndpoint R (baseP g) (L (ProjectiveLine Y)) (L (ProjectiveLine Y')) mP
  lineW : PullEndpoint R (baseW g) (L (diagonalSurface Y)) (L (diagonalSurface Y')) mW

/-- The canonical ordinary supported-source map, using the specified diagonal
square and the coefficient-unit endpoint. Source: blueprint closed-support mate
(blueprint: def-sfb-diagonal-coefficient-source-pullback). -/
def sourcePullbackMap
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y)
    (cP : UnitPullEndpoint R (baseP g)) :
    (CondensedRing.upperStar R (baseW g)).obj (source R Y) ⟶ source R Y' :=
  (ordinaryExchange R (diagonalImmersion Y) (diagonalImmersion Y')
    (baseP g) (baseW g) h).app (Mod.regular (condensedRingObj R (ProjectiveLine Y))) ≫
    (CondensedRing.lowerStar R (diagonalImmersion Y')).map cP.iso.hom

/-- The ordinary source, unit and line normalizations in the fixed geometric
base-change square. This constituent does not depend on the two diagonal arrows
or their derived direct-image presentations. Source: blueprint base-change clause
(blueprint: def-sfb-diagonal-coefficient-source-pullback). -/
structure SourcePullback
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L : ∀ X : Scheme.{u}, Modules R X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X) where
  geometry : BaseSquares g
  endpoints : PullbackEndpoints R g L mP mW
  supported : (CondensedRing.upperStar R (baseW g)).obj (source R Y) ≅ source R Y'
  supported_normalization : supported.hom =
    sourcePullbackMap R g geometry.diagonal_square endpoints.cP

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
