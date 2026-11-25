/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # The termwise section tensor map

Source: Stacks, Section 20.31 (Tag 0FKU), the naive cup before Lemma 20.31.3.
The degree maps are coproduct descents of tensorSectionsMap followed by the
sheaf tensor summand inclusions. A named chain identity supplies the proof
component of the actual cochain map; all its data is constructed explicitly.
-/

@[expose] public section

universe u wC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u})

local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

local instance : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance : SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf

local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  hasColimitsOfSizeShrink.{0, 0, u} _

local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
/-- Tensor sections, as a morphism of global-section modules.
Source: Stacks, Tag 0FKU (blueprint: lem-sc-module-cup-naive-map-chain). -/
def moduleCup_sectionTensorMap (M N : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M ⊗
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (M ⊗ N) :=
  ModuleCat.ofHom (tensorSectionsMap M N ⊤)

/-- The section tensor map in degree n, constructed by the total tensor coproduct.
Source: Stacks, Tag 0FKU, the naive product before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-naive-map-chain) -/
def moduleCup_naiveMapComponent
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (n : ℤ) :
    ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) ⊗
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)).X n ⟶
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (K ⊗ L) |>.X n :=
  HomologicalComplex.mapBifunctorDesc (fun i j h ↦
    moduleCup_sectionTensorMap X (K.X i) (L.X j) ≫
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map
        (HomologicalComplex.ιTensorObj K L i j n h))

@[reassoc]
private theorem sectionTensorMap_natural_left
    {M M' N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (f : M ⟶ M') :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f ▷
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj N ≫
      moduleCup_sectionTensorMap X M' N =
        moduleCup_sectionTensorMap X M N ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (f ▷ N) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact (whiskerRight_app_tmulSection f x y).symm

@[reassoc]
private theorem sectionTensorMap_natural_right
    {M N N' : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (g : N ⟶ N') :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M ◁
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map g ≫
      moduleCup_sectionTensorMap X M N' =
        moduleCup_sectionTensorMap X M N ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (M ◁ g) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact (whiskerLeft_app_tmulSection g x y).symm

private theorem naiveMapComponent_summand
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n h ≫
      moduleCup_naiveMapComponent X K L n =
        moduleCup_sectionTensorMap X (K.X i) (L.X j) ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).map
            (HomologicalComplex.ιTensorObj K L i j n h) := by
  exact HomologicalComplex.ι_mapBifunctorDesc _ i j h

private theorem sectionTensorMap_total_comm
    {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ A B : GradedObject ℤ C, A.HasTensor B]
    [∀ A B : GradedObject ℤ D, A.HasTensor B]
    [∀ A B E : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor A B E]
    [∀ A B E : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ A B E]
    [∀ A B E : GradedObject ℤ D, GradedObject.HasGoodTensor₁₂Tensor A B E]
    [∀ A B E : GradedObject ℤ D, GradedObject.HasGoodTensorTensor₂₃ A B E]
    (S : C ⥤ D) [S.Additive]
    (μ : ∀ A B : C, S.obj A ⊗ S.obj B ⟶ S.obj (A ⊗ B))
    (hleft : ∀ {A A' B : C} (f : A ⟶ A'),
      S.map f ▷ S.obj B ≫ μ A' B = μ A B ≫ S.map (f ▷ B))
    (hright : ∀ {A B B' : C} (g : B ⟶ B'),
      S.obj A ◁ S.map g ≫ μ A B' = μ A B ≫ S.map (A ◁ g))
    (K L : CochainComplex C ℤ) :
    let T := S.mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ (a : ∀ n, (T.obj K ⊗ T.obj L).X n ⟶ S.obj ((K ⊗ L).X n))
      (_ : ∀ (i j n : ℤ) (h : i + j = n),
        HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n h ≫ a n =
          μ (K.X i) (L.X j) ≫ S.map (HomologicalComplex.ιTensorObj K L i j n h))
      (n m : ℤ),
      (T.obj K ⊗ T.obj L).d n m ≫ a m = a n ≫ S.map ((K ⊗ L).d n m) := by
  intro T a ha n m
  by_cases hnm : n + 1 = m
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    change i + j = n at hij
    change HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n hij ≫ _ =
      HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n hij ≫ _
    rw [← Category.assoc, CochainComplex.ιTensorObj_d _ _ i j n m hij hnm]
    rw [Preadditive.add_comp, Linear.units_smul_comp]
    simp only [Category.assoc]
    rw [ha (i + 1) j m (by omega), ha i (j + 1) m (by omega)]
    conv_rhs => rw [← Category.assoc, ha i j n hij]
    rw [Category.assoc, ← S.map_comp, CochainComplex.ιTensorObj_d K L i j n m hij hnm]
    simp only [Functor.map_add, Functor.map_units_smul, Functor.map_comp,
      Preadditive.comp_add, Linear.comp_units_smul]
    apply congrArg₂ (· + ·)
    · change (S.map (K.d i (i + 1)) ▷ S.obj (L.X j)) ≫ _ = _
      rw [← Category.assoc, hleft, Category.assoc]
    · apply congrArg (fun f ↦ i.negOnePow • f)
      change (S.obj (K.X i) ◁ S.map (L.d j (j + 1))) ≫ _ = _
      rw [← Category.assoc, hright, Category.assoc]
  · have hn : ¬ (ComplexShape.up ℤ).Rel n m := hnm
    rw [(T.obj K ⊗ T.obj L).shape n m hn, (K ⊗ L).shape n m hn]
    simp

/-- The summandwise section tensor maps commute with the total differentials.
Source: Stacks, Tag 0FKU, the naive product before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-naive-map-chain)
Proof: precompose both sides with every (i,j)-summand inclusion. The total
 differential is the sum of the differential in the first factor and the signed
 differential in the second factor. Tensor sections commute with each factor's
 morphism by tensorHom_app_tmulSection. Sections is additive, so it preserves
 the sum and the integer sign. Thus both sides agree on pure tensors in each
 summand. TensorProduct.ext and the coproduct universal property give equality.
This uses all integer degrees, including negative ones, without boundedness. -/
theorem moduleCup_naiveMap_comm
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (n m : ℤ) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    (T.obj K ⊗ T.obj L).d n m ≫ moduleCup_naiveMapComponent X K L m =
      moduleCup_naiveMapComponent X K L n ≫ (T.obj (K ⊗ L)).d n m := by
  exact sectionTensorMap_total_comm (RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (moduleCup_sectionTensorMap X) (fun f ↦ sectionTensorMap_natural_left X f)
    (fun g ↦ sectionTensorMap_natural_right X g) K L
    (moduleCup_naiveMapComponent X K L) (naiveMapComponent_summand X K L) n m


/-- The actual naive section tensor cochain map.
Source: Stacks, Tag 0FKU, the naive product before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-naive-map-chain) -/
def moduleCup_naiveMap
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    T.obj K ⊗ T.obj L ⟶ T.obj (K ⊗ L) where
  f := moduleCup_naiveMapComponent X K L
  comm' := fun n m _ ↦ (moduleCup_naiveMap_comm X K L n m).symm

/-- The explicit naive map tensors sections on every coproduct summand. -/
theorem moduleCup_naiveMap_summand
    (K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (i j n : ℤ) (h : i + j = n) (x : Γ(K.X i, ⊤)) (y : Γ(L.X j, ⊤)) :
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ((moduleCup_naiveMap X K L).f n).hom
        ((HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n h).hom
          (TensorProduct.tmul Γ(X, ⊤) x y)) =
      (HomologicalComplex.ιTensorObj K L i j n h).val.app (op ⊤)
        (tmulSection x y) := by
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have e := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := T.obj K) (K₂ := T.obj L) (F := curriedTensor _) (c := ComplexShape.up ℤ)
    (fun a b hab ↦
      (show (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (K.X a) ⊗
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (L.X b) ⟶
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj (K.X a ⊗ L.X b) from
        ModuleCat.ofHom (tensorSectionsMap (K.X a) (L.X b) ⊤)) ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).map
          (HomologicalComplex.ιTensorObj K L a b n hab)) i j h
  exact congrArg (fun f ↦ f.hom (TensorProduct.tmul Γ(X, ⊤) x y)) e


end
end AlgebraicGeometry.Scheme.Modules
