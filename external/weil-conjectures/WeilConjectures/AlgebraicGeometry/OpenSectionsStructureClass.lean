/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenSectionsCohomologyModel
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.DerivedStructureEvaluationOne
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.OpenSectionsOrdinaryStructureClass

/-! # The ordinary restricted structure class

Source: Stacks Project, Tags 06Z0 and 079V.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Extend the single A-module complex and identify its tilde with the structure single. -/
def openComparisonStructureComplexIso (A : Type u) [CommRing A] :
    let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
    ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat) ≅
      (CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) := by
  let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
  let e : K.extend ComplexShape.embeddingDownNat ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of A A) 0 0 rfl
  exact ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).mapIso e ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (koszulOpenTilde A) (.up ℤ) 0).app
      (ModuleCat.of A A)

private theorem complexUnit_homology_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (S : C ⥤ D) [S.Additive] {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    HomologicalComplex.homologyMap ((S.mapHomologicalComplex (.up ℤ)).map f) 0 ≫
        ((DerivedCategory.homologyFunctorFactors D 0).app
          ((S.mapHomologicalComplex (.up ℤ)).obj L)).inv ≫
        (DerivedCategory.homologyFunctor D 0).map ((openComparisonComplexUnit S).app L) =
      ((DerivedCategory.homologyFunctorFactors D 0).app
          ((S.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
        (DerivedCategory.homologyFunctor D 0).map ((openComparisonComplexUnit S).app K) ≫
        (DerivedCategory.homologyFunctor D 0).map
          (S.rightDerivedFunctor.map (DerivedCategory.Q.map f)) := by
  let H := DerivedCategory.homologyFunctor D 0
  have h₁ := (DerivedCategory.homologyFunctorFactors D 0).inv.naturality
    ((S.mapHomologicalComplex (.up ℤ)).map f)
  have h₂ := congrArg (fun k ↦ H.map k) ((openComparisonComplexUnit S).naturality f)
  dsimp only [Functor.comp_map] at h₁ h₂
  simp only [Functor.map_comp] at h₂
  change HomologicalComplex.homologyMap _ 0 ≫ _ = _ at h₁
  calc
    _ = _ := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k ↦ k ≫ H.map ((openComparisonComplexUnit S).app L)) h₁
    _ = _ := Category.assoc _ _ _
    _ = _ := congrArg (fun k ↦
      ((DerivedCategory.homologyFunctorFactors D 0).app
        ((S.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫ k) h₂

private theorem exact_single_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {K : CochainComplex C ℤ} {X : C} {Y : D}
    (a : K ≅ (CochainComplex.singleFunctor C 0).obj X) (b : T.obj X ≅ Y) :
    let e := (T.mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
      (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app X ≪≫
      (CochainComplex.singleFunctor D 0).mapIso b
    let i := T.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso a) ≪≫
      (T.mapDerivedCategorySingleFunctor 0).app X ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso b
    i.inv = DerivedCategory.Q.map e.inv ≫ T.mapDerivedCategoryFactors.inv.app K := by
  intro e i
  apply (cancel_mono (T.mapDerivedCategoryFactors.hom.app K)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  dsimp only [i, e, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
  rw [Category.assoc, T.mapDerivedCategoryFactors_hom_naturality]
  simp only [Category.assoc]
  erw [T.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  erw [Category.comp_id]
  rfl

private theorem exact_single_complexUnit_apply
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    {R : Type u} [Ring R] [HasDerivedCategory (ModuleCat.{u} R)]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (S : D ⥤ ModuleCat.{u} R) [S.Additive]
    {K : CochainComplex C ℤ} {X : C} {Y : D}
    (a : K ≅ (CochainComplex.singleFunctor C 0).obj X) (b : T.obj X ≅ Y)
    (x : ((S.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor D 0).obj Y)).homology 0) :
    let J := (T.mapHomologicalComplex (.up ℤ)).obj K
    let L := (CochainComplex.singleFunctor D 0).obj Y
    let e := (T.mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
      (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app X ≪≫
      (CochainComplex.singleFunctor D 0).mapIso b
    let i := T.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso a) ≪≫
      (T.mapDerivedCategorySingleFunctor 0).app X ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso b
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
    let F := S.rightDerivedFunctor ⋙ H
    let Φ := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0
    F.map i.inv
        (H.map ((openComparisonComplexUnit S).app L)
          ((Φ.app ((S.mapHomologicalComplex (.up ℤ)).obj L)).inv x)) =
      F.map (T.mapDerivedCategoryFactors.inv.app K)
        (H.map ((openComparisonComplexUnit S).app J)
          ((Φ.app ((S.mapHomologicalComplex (.up ℤ)).obj J)).inv
            (HomologicalComplex.homologyMap
              ((S.mapHomologicalComplex (.up ℤ)).map e.inv) 0 x))) := by
  intro J L e i H F Φ
  have hn := congrArg (fun f ↦ f x) (complexUnit_homology_naturality S e.inv)
  simp only [ModuleCat.comp_apply] at hn
  rw [exact_single_iso T a b, F.map_comp, ModuleCat.comp_apply]
  exact congrArg (fun z ↦ F.map (T.mapDerivedCategoryFactors.inv.app K) z) hn.symm

/-- Before comparing the two derived functors, the restricted structure class is the
image of the ordinary tilde class of one under the restricted ordinary-to-derived unit.
Source: Stacks Project, Tag 06Z0, the tilde/sections unit, and Tag 079V, the definition
of derived global sections on an ordinary complex.
(blueprint: lem-sc-open-sections-structure-class).

Proof: The extended single complex is identified with the integer single complex by
extendSingleIso. Its homology identification is extendHomologyIso followed by
singleObjHomologySelfIso. Apply tilde and then restriction. The derived single-functor
comparison and sheafOfModulesEquivOverUnit identify this with O_U[0], giving i.
On ordinary degree-zero sections the latter unit isomorphism takes the restricted
structure section one to the section one. Under openComparisonSectionsIso this is
exactly tilde.toOpen of one: the tildeSelf identification, the single-map comparison,
and extendHomologyIso all take the degree-zero class of one to one, and restriction
of the structure sheaf takes one to one. Exact scalar forgetting identifies the same
cycle class through openComparisonOrdinaryIso. Naturality of the ordinary-to-derived
global-sections unit with the complex isomorphism, and naturality of homologyFunctorFactors,
transport this ordinary equality to the displayed derived equality. This calculation
uses neither a comparison equivalence between the two derived section computations nor
an assertion about Hom sets. If U is empty or A is the zero ring, all classes are zero
and the same cycle calculation applies.
-/
theorem openComparison_structure_class (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    let T := openComparisonRestriction A U
    let F := openComparisonGlobalCohomology A U
    let O := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace))
    let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
    let L := K.extend ComplexShape.embeddingDownNat
    let C := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj L
    let η₀ : 𝟭 (ModuleCat.{u} A) ⟶ koszulOpenTilde A ⋙ affineOpenSections A U :=
      { app := fun M ↦ tilde.toOpen M U
        naturality := fun _ _ g ↦ (tilde.toOpen_map_app g U).symm }
    let η := (NatTrans.mapHomologicalComplex η₀ (.up ℤ)).app L
    let j : L.homology 0 ≅ ModuleCat.of A A :=
      K.extendHomologyIso ComplexShape.embeddingDownNat (j := 0) rfl ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (ModuleCat.of A A)
    let i : T.mapDerivedCategory.obj (koszulOpenStructure A) ≅ O :=
      T.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso
        (openComparisonStructureComplexIso A)) ≪≫
      (T.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).mapIso
          (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U _)
    F.map i.inv (derivedStructureGlobalOne U.toScheme) =
      openComparisonRestrictedUnit A U C
        ((HomologicalComplex.homologyMap η 0) (j.inv (1 : A))) := by
  intro T F O K L C η₀ η j i
  let B := (moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  let S := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let Φ := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 0
  let J := (T.mapHomologicalComplex (.up ℤ)).obj C
  let V := (S.mapHomologicalComplex (.up ℤ)).obj J
  let D := (CochainComplex.singleFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
      (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace))
  let e : J ≅ D :=
    (T.mapHomologicalComplex (.up ℤ)).mapIso (openComparisonStructureComplexIso A) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app _ ≪≫
      (CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).mapIso
          (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U _)
  let VD := (S.mapHomologicalComplex (.up ℤ)).obj D
  let ε : VD.homology 0 ≅ ModuleCat.of B B :=
    (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) 0).app _) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of B B)
  have ho : HomologicalComplex.homologyMap
      ((S.mapHomologicalComplex (.up ℤ)).map e.inv) 0 (ε.inv (1 : B)) =
      (openComparisonOrdinaryIso A U C).inv
        ((HomologicalComplex.homologyMap η 0) (j.inv (1 : A))) := by
    exact openComparison_ordinary_structure_class A U
  calc
    _ = F.map (T.mapDerivedCategoryFactors.inv.app C)
        (H.map ((openComparisonComplexUnit S).app J)
          ((Φ.app V).inv
            (HomologicalComplex.homologyMap
              ((S.mapHomologicalComplex (.up ℤ)).map e.inv) 0 (ε.inv (1 : B))))) :=
      exact_single_complexUnit_apply T S (openComparisonStructureComplexIso A)
        (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U _) (ε.inv (1 : B))
    _ = _ := congrArg (fun z ↦ F.map (T.mapDerivedCategoryFactors.inv.app C)
      (H.map ((openComparisonComplexUnit S).app J) ((Φ.app V).inv z))) ho

end
end AlgebraicGeometry
