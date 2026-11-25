/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
/-! # Sources and projective models for the completed trace
Source: blueprint main-20261015, sk-prop-diagonal-tower-trace, proof steps 1--8
(blueprint: proposition-ell-adic-cycle-class-diagonal).

## Main declarations
- `diagonalTraceFirstModel` and `diagonalTraceSecondModel` specify both product projections.
- `DiagonalTrace.NormalizedSource` and `DiagonalTrace.SupportedSource` fix the supported source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u w v a b c va vb vc wa wb wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The specified projective-line model of the first product projection.
Source: blueprint trace clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalTraceFirstModel (Y : Scheme.{u}) :
    diagonalSurface Y ≅ ProjectiveLine (ProjectiveLine Y) :=
  ((ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2))
    (ProjectiveLine Y ↘ Y)).flip.isoPullback).symm

/-- The second projective-line model uses the canonical factor interchange.
Source: blueprint trace clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalTraceSecondModel (Y : Scheme.{u}) :
    diagonalSurface Y ≅ ProjectiveLine (ProjectiveLine Y) :=
  pullbackSymmetry (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ≪≫
    diagonalTraceFirstModel Y

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- Normalized source data for an ordinary direct image and its right derived functor.
The predicate fixes the ordinary comparison; the last field asserts its acyclicity.
Source: blueprint trace proof step 9 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
structure NormalizedSource
    {A : Type a} {B : Type a} [Category.{va} A] [Category.{va} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (R : DiagonalRightDerived F) (M : A) (N : B)
    (P : Prop) (normalizes : (N ≅ F.obj M) → P → Prop) where
  over_eq : P
  iso : N ≅ F.obj M
  normalization : normalizes iso over_eq
  acyclic : IsIso (diagonalTraceRightSingle F R M)

/-- The canonical map from a normalized coefficient source to its derived direct image.
Source: blueprint trace proof step 9 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def NormalizedSource.hom
    {A : Type a} {B : Type a} [Category.{va} A] [Category.{va} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    {F : A ⥤ B} [F.Additive] {R : DiagonalRightDerived F} {M : A} {N : B}
    {P : Prop} {normalizes : (N ≅ F.obj M) → P → Prop}
    (s : NormalizedSource F R M N P normalizes) :
    (DerivedCategory.singleFunctor B 0).obj N ⟶
      R.R.obj ((DerivedCategory.singleFunctor A 0).obj M) :=
  (DerivedCategory.singleFunctor B 0).map s.iso.hom ≫ diagonalTraceRightSingle F R M

/-- The integration identity for a specified source comparison and trace.
Source: blueprint trace clause 2 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def IsIntegration
    {C : Type a} {D : Type b} [Category.{va} C] [Category.{vb} D]
    (R : C ⥤ D) {M N : C} {K : D} (a : K ⟶ R.obj M) (t : R.obj N ⟶ K)
    (δ : M ⟶ N) : Prop := a ≫ R.map δ ≫ t = 𝟙 K

/-- The ordinary supported-source identification is normalized by actual composition
of additive direct images, the equality f Delta = id, and the identity direct image.
Source: blueprint trace proof step 9 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def supportedSourceNormalization (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (i : SheafOfModules.unit
      (Scheme.purTwistRing (ProjectiveLine Y) (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)) ≅
      (diagonalTracePush l f).obj (diagonalCompletedSource l Y))
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) : Prop :=
  HEq ((diagonalCompletedRestriction l (ProjectiveLine Y) ⋙
      diagonalForget l (ProjectiveLine Y)).map i.inv)
    (((lowerStarComp AddCommGrpCat.{u + 1} (diagonalImmersion Y) f) ≪≫
      lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫
      lowerStarId AddCommGrpCat.{u + 1} (ProjectiveLine Y)).hom.app
        ((diagonalCompletedRestriction l (ProjectiveLine Y) ⋙
          diagonalForget l (ProjectiveLine Y)).obj
            (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
              (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))))

/-- The source identification Rf_* Delta_* Z_l = Z_l uses the specified ordinary
composition map and the universal derived unit, which is invertible on this source.
Source: blueprint trace clause 2 and proof step 9
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev SupportedSource (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l (ProjectiveLine Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y))]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    [(diagonalTracePush l f).Additive]
    (R : DiagonalRightDerived (diagonalTracePush l f)) :=
  NormalizedSource (diagonalTracePush l f) R (diagonalCompletedSource l Y)
    (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))
    (diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (supportedSourceNormalization l Y f)

end AlgebraicGeometry.ProEtale.DiagonalTrace
