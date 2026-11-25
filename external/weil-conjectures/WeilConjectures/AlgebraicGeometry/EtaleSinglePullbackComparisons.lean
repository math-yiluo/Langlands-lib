/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGenerators
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import all Mathlib.Logic.Small.Defs
/-!
# Canonical single-complex pullback comparisons

The constant and shifted coefficient comparisons are constructed for a general
coefficient category before specializing them to modules. This caches their
structural instances and avoids comparing separate expanded derived constructions.
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
/-- The canonical constant pullback comparison, cached for a general coefficient category. -/
def constantSinglePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M : B) :
    (upperStar B f).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology B).obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology B).obj M) :=
  genericConstantIso B M f

/-- Components of the cached constant comparison are the original single-object maps. -/
theorem constantSinglePullbackIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (M : B) :
    (constantSinglePullbackIso B f M).hom =
      (singleFunctorCompLeftDerivedUpperStarIso B f).hom.app
          ((constantSheaf Y.smallEtaleTopology B).obj M) ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((Scheme.upperStarConstantSheafIso B f).hom.app M) := by
  rfl

/-- The cached comparison has the same component as the source's constant comparison. -/
theorem constantSinglePullbackIso_source_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (M : B) :
    (constantSinglePullbackIso B f M).hom =
      (leftDerivedUpperStarSingleConstantSheafIso B f M).hom := by
  rw [constantSinglePullbackIso_hom]
  exact Category.assoc
    ((leftDerivedUpperStarIsoMapDerivedCategory B f).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology B).obj M)))
    (((upperStar B f).mapDerivedCategorySingleFunctor 0).hom.app
      ((constantSheaf Y.smallEtaleTopology B).obj M))
    ((DerivedCategory.singleFunctor _ 0).map
      ((Scheme.upperStarConstantSheafIso B f).hom.app M))

/-- Shift the specified single-degree comparison without reconstructing its functors. -/
def shiftedSinglePullbackIsoWith (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sY : Sheaf Y.smallEtaleTopology B ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (sX : Sheaf X.smallEtaleTopology B ⥤ DerivedCategory (Sheaf X.smallEtaleTopology B))
    (c : sY ⋙ (upperStar B f).leftDerivedFunctor ≅ upperStar B f ⋙ sX)
    (J : Sheaf Y.smallEtaleTopology B) (J' : Sheaf X.smallEtaleTopology B)
    (e : (upperStar B f).obj J ≅ J') (n : ℤ) :
    (upperStar B f).leftDerivedFunctor.obj ((sY.obj J)⟦n⟧) ≅ (sX.obj J')⟦n⟧ :=
  letI := commShiftLeftDerivedUpperStar B f
  (((upperStar B f).leftDerivedFunctor.commShiftIso n).app _) ≪≫
    (shiftFunctor _ n).mapIso (c.app J ≪≫ sX.mapIso e)

/-- The two single-object units attached to a section, before coefficient specialization. -/
def constantSingleSectionUnits {X Y : Scheme.{u}}
    (s : Y ⟶ X) (p : X ⟶ Y) (M : B) :
    (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology B).obj M) ⟶
      (lowerStar B p).rightDerivedFunctor.obj
        ((lowerStar B s).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf Y.smallEtaleTopology B).obj M))) :=
  Adjunction.derivedSingleUnit (upperStarLowerStarAdjunction B p)
      ((constantSheaf Y.smallEtaleTopology B).obj M)
      ((constantSheaf X.smallEtaleTopology B).obj M)
      ((Scheme.upperStarConstantSheafIso B p).hom.app M) ≫
    (lowerStar B p).rightDerivedFunctor.map
      (Adjunction.derivedSingleUnit (upperStarLowerStarAdjunction B s)
        ((constantSheaf X.smallEtaleTopology B).obj M)
        ((constantSheaf Y.smallEtaleTopology B).obj M)
        ((Scheme.upperStarConstantSheafIso B s).hom.app M))

end AlgebraicGeometry.Etale
