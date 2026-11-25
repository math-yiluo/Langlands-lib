/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Canonical derived global germs

Source: Stacks Project, Tags 03QO, 01EZ and 095T.
(blueprint: def-weil-pbc-derived-global-germ)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme

attribute [local instance] GrothendieckTopology.Point.sheafFiber_additive

noncomputable local instance instAB5OfSizeAddCommGrpCat_derivedGlobalGerm
    : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

/-- The global germ, using the terminal object of the small etale site. 
(blueprint: def-weil-pbc-derived-global-germ)
-/
noncomputable def globalGerm {Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y) :
    Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⟶
      (pointSmallEtale t).sheafFiber :=
  (Sheaf.ΓNatIsoSheafSections _ _
    (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) Y)).hom ≫
    Functor.whiskerLeft (sheafToPresheaf _ _)
      ((pointSmallEtale t).toPresheafFiberNatTrans (Scheme.Etale.mk (𝟙 Y))
        (Over.homMk t (Category.comp_id t)))

/-- The germ at the image point, transported to the inverse-image stalk. 
(blueprint: def-weil-pbc-derived-global-germ)
-/
noncomputable def pulledGlobalGerm {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y') :
    Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⟶
      (g)^*[AddCommGrpCat.{u + 1}] ⋙ (pointSmallEtale t).sheafFiber :=
  globalGerm (t ≫ g) ≫ (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} g t).inv

/-- Derive the global germ after Leray. Its construction has no strict-local hypothesis.
Source: Stacks Project, Tags 03QO and 01EZ.
(blueprint: def-weil-pbc-derived-global-germ) -/
noncomputable def derivedPulledGlobalGerm {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y') :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⟶
      (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
        (g)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
          (pointSmallEtale t).sheafFiber.mapDerivedCategoryPlus := by
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
  exact (Functor.rightDerivedFunctorPlusCompIso' _ _
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f)).inv ≫
    Functor.whiskerLeft (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusNatTrans (pulledGlobalGerm g t) ≫
        ((g)^*[AddCommGrpCat.{u + 1}] ⋙
          (pointSmallEtale t).sheafFiber).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom ≫
        (Functor.mapDerivedCategoryPlusCompIso _ _).hom)

/-- Derive the global germ after Leray, without an intervening inverse image. 
(blueprint: def-weil-pbc-derived-global-germ)
-/
noncomputable def derivedGlobalGerm {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⟶
      (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
        (pointSmallEtale t).sheafFiber.mapDerivedCategoryPlus := by
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
  exact (Functor.rightDerivedFunctorPlusCompIso' _ _
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f)).inv ≫
    Functor.whiskerLeft (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusNatTrans (globalGerm t) ≫
        (pointSmallEtale t).sheafFiber.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom)

/-- If the underived pulled global germ is invertible, so is its derived comparison. 
(blueprint: def-weil-pbc-derived-global-germ)
-/
theorem isIso_derivedPulledGlobalGerm {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    [IsIso (pulledGlobalGerm g t)] : IsIso (derivedPulledGlobalGerm f g t) := by
  unfold derivedPulledGlobalGerm
  infer_instance

/-- If the underived global germ is invertible, so is its derived comparison. 
(blueprint: def-weil-pbc-derived-global-germ)
-/
theorem isIso_derivedGlobalGerm {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    [IsIso (globalGerm t)] : IsIso (derivedGlobalGerm f t) := by
  unfold derivedGlobalGerm
  infer_instance

end AlgebraicGeometry.Etale
