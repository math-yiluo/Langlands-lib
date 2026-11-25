/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleHomComparisonCore
public import WeilConjectures.CategoryTheory.HomComparison.HomComparisonEquivalence

/-! # Bifunctor form of the normalized native section Hom comparison

## References

* Stacks 03EO
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.NativeFrobenius
variable (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The two-variable native internal Hom functor. -/
def nativeHom : (AdicSheaf l Y)ᵒᵖ × AdicSheaf l Y ⥤ AdicSheaf l Y :=
  Functor.uncurry.obj
    { obj := fun M ↦ AdicSheaf.ihom M.unop
      map := fun f ↦ Mod.ihomMap f.unop
      map_id := fun M ↦ Mod.ihomMap_id M.unop
      map_comp := fun f h ↦ Mod.ihomMap_comp h.unop f.unop }

attribute [local irreducible] comparisonModuleFunctor comparisonRing
  SheafOfModules.homObjMap

/-- The normalized forward native Hom comparison as a single bifunctor isomorphism. -/
def forwardHomComparison (H : AdicModuleHomComparisonCore l Y) :
    nativeHom Y l ⋙ (adicSectionModuleEquivalence l Y).functor ≅
      (adicSectionModuleEquivalence l Y).functor.op.prod
        (adicSectionModuleEquivalence l Y).functor ⋙
          Functor.uncurry.obj (SheafOfModules.homFunctor (comparisonRing l Y)) :=
  NatIso.ofComponents
    (F := nativeHom Y l ⋙ (adicSectionModuleEquivalence l Y).functor)
    (G := (adicSectionModuleEquivalence l Y).functor.op.prod
      (adicSectionModuleEquivalence l Y).functor ⋙
        Functor.uncurry.obj (SheafOfModules.homFunctor (comparisonRing l Y)))
    (fun MN ↦ (H.homIso MN.1.unop).app MN.2)
    (fun {MN MN'} f ↦ by
      change (comparisonModuleFunctor l Y).map
          ((Mod.ihomMap f.1.unop).app MN.2 ≫
            (AdicSheaf.ihom MN'.1.unop).map f.2) ≫ _ =
        _ ≫ (SheafOfModules.homObjMap (R := comparisonRing l Y)
            ((comparisonModuleFunctor l Y).map f.1.unop) (𝟙 _) ≫
          SheafOfModules.homObjMap (R := comparisonRing l Y) (𝟙 _)
            ((comparisonModuleFunctor l Y).map f.2))
      simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]
      exact H.hom_naturality f.1.unop f.2)

attribute [local irreducible] nativeHom adicSectionModuleEquivalence

/-- The Hom comparison reversed along the native section equivalence. -/
def inverseNativeHomComparison (H : AdicModuleHomComparisonCore l Y) :
    Functor.uncurry.obj (SheafOfModules.homFunctor (comparisonRing l Y)) ⋙
        (adicSectionModuleEquivalence l Y).inverse ≅
      (adicSectionModuleEquivalence l Y).inverse.op.prod
        (adicSectionModuleEquivalence l Y).inverse ⋙ nativeHom Y l :=
  HomComparison.inverseHomComparison (adicSectionModuleEquivalence l Y)
    (Functor.uncurry.obj (SheafOfModules.homFunctor (comparisonRing l Y)))
    (nativeHom Y l) (forwardHomComparison Y l H)

end AlgebraicGeometry.ProEtale.NativeFrobenius
