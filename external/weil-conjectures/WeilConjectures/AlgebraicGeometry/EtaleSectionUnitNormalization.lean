/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Constant-unit normalization along sections -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem hom_square_of_inv_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {U V : D} (x : X ≅ Y) (y : U ≅ V)
    (a : F.obj X ⟶ U) (b : F.obj Y ⟶ V)
    (h : F.map x.inv ≫ a = b ≫ y.inv) :
    F.map x.hom ≫ b = a ≫ y.hom := by
  apply (cancel_epi (F.map x.inv)).mp
  rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Generic
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 21000] sheafBraidedCategory
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarCompSectionIso singleFunctorObjUnitIso
  leftDerivedUpperStarSingleConstantSheafIso
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
/-- The section comparison is compatible with the monoidal unit. -/
theorem sectionPullback_unit {X Y : Scheme.{u}}
    (s : Y ⟶ X) (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y) :
    (upperStar B s).leftDerivedFunctor.map (leftDerivedUpperStarUnitIso B p).hom ≫
        (leftDerivedUpperStarUnitIso B s).hom =
      (leftDerivedUpperStarCompSectionIso B s p h).hom.app (𝟙_ _) := by
  let := leftDerivedUpperStarOplaxMonoidal B p
  let := leftDerivedUpperStarOplaxMonoidal B s
  let F : DerivedCategory (Sheaf Y.smallEtaleTopology B) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology B) := (upperStar B p).leftDerivedFunctor
  let G : DerivedCategory (Sheaf X.smallEtaleTopology B) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology B) := (upperStar B s).leftDerivedFunctor
  let d : (Functor.postcompose₂.obj (F ⋙ G)).obj
        (curriedTensor (DerivedCategory (Sheaf Y.smallEtaleTopology B))) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F ⋙ G)).obj (F ⋙ G)).obj
        (curriedTensor (DerivedCategory (Sheaf Y.smallEtaleTopology B))) :=
    { app M :=
        { app N := Functor.OplaxMonoidal.δ (F ⋙ G) M N
          naturality := fun _ _ f ↦
            (Functor.OplaxMonoidal.δ_natural_right (F ⋙ G) M f).symm }
      naturality := fun _ _ f ↦ by
        ext N
        exact (Functor.OplaxMonoidal.δ_natural_left (F ⋙ G) f N).symm }
  have hp := isIso_leftDerivedUpperStarOplaxMonoidal_δ B p (𝟙_ _) (𝟙_ _)
  have hs := isIso_leftDerivedUpperStarOplaxMonoidal_δ B s (F.obj (𝟙_ _)) (F.obj (𝟙_ _))
  have : IsIso ((d.app (𝟙_ _)).app (𝟙_ _)) := by
    change IsIso (G.map (Functor.OplaxMonoidal.δ F (𝟙_ _) (𝟙_ _)) ≫
      Functor.OplaxMonoidal.δ G (F.obj (𝟙_ _)) (F.obj (𝟙_ _)))
    infer_instance
  have : Epi ((d.app (𝟙_ _)).app (𝟙_ _)) := inferInstance
  have ht := sectionPullback_tensor B s p h (𝟙_ _) (𝟙_ _)
  have he : Functor.OplaxMonoidal.η (F ⋙ G) =
      G.map (leftDerivedUpperStarUnitIso B p).hom ≫
        (leftDerivedUpperStarUnitIso B s).hom := by
    change G.map (Functor.OplaxMonoidal.η F) ≫ Functor.OplaxMonoidal.η G = _
    dsimp only [F, G]
    erw [leftDerivedUpperStarOplaxMonoidal_η, leftDerivedUpperStarOplaxMonoidal_η]
  have : IsIso (Functor.OplaxMonoidal.η (F ⋙ G)) := by
    rw [he]
    infer_instance
  rw [← he]
  apply Adjunction.unit_compatibility_of_tensor (F ⋙ G) d
    (leftDerivedUpperStarCompSectionIso B s p h) (Functor.OplaxMonoidal.η (F ⋙ G))
  · simpa only [d, Functor.OplaxMonoidal.comp_δ, F, G,
      canonicalPullbackTensorComparison_app_eq_delta, Category.assoc] using ht
  · exact Functor.OplaxMonoidal.left_unitality_hom (F ⋙ G) (𝟙_ _)
omit [UpperStarPreservesFlat B] in
/-- The constant-object pullback comparison agrees with the monoidal unit comparison. -/
theorem pullback_singleUnit_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar B f).leftDerivedFunctor.map (singleFunctorObjUnitIso B Y).hom ≫
        (leftDerivedUpperStarUnitIso B f).hom =
      (leftDerivedUpperStarSingleConstantSheafIso B f (𝟙_ B)).hom ≫
        (singleFunctorObjUnitIso B X).hom := by
  exact hom_square_of_inv_square (upperStar B f).leftDerivedFunctor
    (singleFunctorObjUnitIso B Y) (singleFunctorObjUnitIso B X)
    (leftDerivedUpperStarSingleConstantSheafIso B f (𝟙_ B)).hom
    (leftDerivedUpperStarUnitIso B f).hom
    (leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp B f)

/-- Two normalized constant pullbacks around a section give its canonical comparison. -/
theorem sectionPullback_singleUnit {X Y : Scheme.{u}}
    (s : Y ⟶ X) (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y) :
    (upperStar B s).leftDerivedFunctor.map
        (leftDerivedUpperStarSingleConstantSheafIso B p (𝟙_ B)).hom ≫
      (leftDerivedUpperStarSingleConstantSheafIso B s (𝟙_ B)).hom =
      (leftDerivedUpperStarCompSectionIso B s p h).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology B).obj (𝟙_ B))) := by
  apply (cancel_mono (singleFunctorObjUnitIso B Y).hom).mp
  erw [Category.assoc, ← pullback_singleUnit_hom,
    ← Functor.map_comp_assoc, ← pullback_singleUnit_hom, Functor.map_comp]
  rw [Category.assoc, sectionPullback_unit]
  exact (leftDerivedUpperStarCompSectionIso B s p h).hom.naturality
    (singleFunctorObjUnitIso B Y).hom

omit [UpperStarPreservesFlat B] in
/-- The derived constant unit is the adjunction unit followed by constant comparison. -/
theorem derivedConstantUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : B) :
    Adjunction.derivedSingleUnit (upperStarLowerStarAdjunction B f)
      ((constantSheaf Y.smallEtaleTopology B).obj M)
      ((constantSheaf X.smallEtaleTopology B).obj M)
      ((Scheme.upperStarConstantSheafIso B f).hom.app M) =
    (derivedUpperStarLowerStarAdjunction B f).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology B).obj M)) ≫
      (lowerStar B f).rightDerivedFunctor.map
        (leftDerivedUpperStarSingleConstantSheafIso B f M).hom := by
  rw [Adjunction.derivedSingleUnit_eq, ← constantSinglePullbackIso_source_hom,
    constantSinglePullbackIso_hom]
  unfold derivedUpperStarLowerStarAdjunction
  rfl

omit [UpperStarPreservesFlat B] in
/-- The expanded single-object constant comparison preserves the tensor unit. -/
theorem constantUnitPullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar B f).leftDerivedFunctor.map (singleFunctorObjUnitIso B Y).hom ≫
        (leftDerivedUpperStarUnitIso B f).hom =
      (constantSinglePullbackIso B f (𝟙_ B)).hom ≫
        (singleFunctorObjUnitIso B X).hom := by
  rw [constantSinglePullbackIso_source_hom]
  change (upperStar B f).leftDerivedFunctor.map (singleFunctorObjUnitIso B Y).hom ≫
      (leftDerivedUpperStarUnitIso B f).hom =
    (leftDerivedUpperStarSingleConstantSheafIso B f (𝟙_ B)).hom ≫
      (singleFunctorObjUnitIso B X).hom
  exact pullback_singleUnit_hom B f

/-- The cached pair of constant units is the canonical section comparison. -/
theorem constantSingleSectionUnits_eq {X Y : Scheme.{u}}
    (s : Y ⟶ X) (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y) :
    constantSingleSectionUnits B s p (𝟙_ B) =
      (derivedSectionPushIso B s p h).hom.app
        (constantSingle B Y (𝟙_ B)) := by
  unfold constantSingleSectionUnits
  rw [derivedConstantUnit_eq, derivedConstantUnit_eq]
  exact Adjunction.pasted_units_section
    (derivedUpperStarLowerStarAdjunction B p) (derivedUpperStarLowerStarAdjunction B s)
    (leftDerivedUpperStarCompSectionIso B s p h)
    (leftDerivedUpperStarSingleConstantSheafIso B p (𝟙_ B)).hom
    (leftDerivedUpperStarSingleConstantSheafIso B s (𝟙_ B)).hom
    (sectionPullback_singleUnit B s p h)

end Generic

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 21000] sheafBraidedCategory
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  singleFunctorCompLeftDerivedUpperStarIso singleFunctorObjUnitIso
  leftDerivedUpperStarSingleConstantSheafIso

/-- The recorded diagonal integral source is the canonical conjugate section unit. -/
theorem projectiveLineDiagonalAlpha_eq (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    projectiveLineDiagonalAlpha A S a =
      (derivedSectionPushIso (ModuleCat.{u + 1} A)
        (pullback.diagonal (ProjectiveLine S ↘ S)) (projectiveLineDiagonalProjection S a)
        (by cases a <;> simp [projectiveLineDiagonalProjection])).hom.app
        (ordinaryFiniteUnit A (ProjectiveLine S)) := by
  delta projectiveLineDiagonalAlpha
  exact constantSingleSectionUnits_eq (ModuleCat.{u + 1} A)
    (pullback.diagonal (ProjectiveLine S ↘ S)) (projectiveLineDiagonalProjection S a)
    (by cases a <;> simp [projectiveLineDiagonalProjection])

end AlgebraicGeometry.Etale
