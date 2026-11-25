/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# Tensor product and internal hom of modules over a commutative monoid

Let `A` be a commutative monoid object in a braided monoidal category `C`. For `A`-modules `M`
and `P`, the tensor product `P ⊗_A M` is the coequalizer of the two maps
`P ⊗ (A ⊗ M) ⇉ P ⊗ M`, acting by `A` on `M`, respectively by `A` on `P` from the right; it is an
`A`-module through `P` (`CategoryTheory.Mod.tensorLeft`). When `C` is abelian and Grothendieck,
monoidal closed, and `A ⊗ -` commutes with colimits, `- ⊗_A M` commutes with colimits, so it has
a right adjoint `Hom_A(M, -)` (`CategoryTheory.Mod.ihom`), by the special adjoint functor theorem:
the internal hom of `A`-modules.

## Main definitions

- `CategoryTheory.Mod.tensorRight`: `P ↦ P ⊗ X`, an `A`-module through `P`.
- `CategoryTheory.Mod.tensorLeft`: `P ↦ P ⊗_A M`.
- `CategoryTheory.Mod.ihom`: `Hom_A(M, -)`, right adjoint to `- ⊗_A M`.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

section TensorRight

/-- The `A`-module structure on `P ⊗ X`, acting on `P`. -/
@[implicit_reducible]
def tensorRightModObj (P : Mod C A) (X : C) : ModObj A (P.X ⊗ X) :=
  .mk' A ((α_ A P.X X).inv ≫ act P.X ▷ X)
    (by rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, one_act,
      leftUnitor_tensor_hom])
    (by
      rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, mul_act,
        MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc]
      simp only [comp_whiskerRight]
      monoidal)

variable (A) in
/-- The functor `P ↦ P ⊗ X` on `A`-modules, `A` acting on `P`. -/
@[simps!]
def tensorRight (X : C) : Mod C A ⥤ Mod C A where
  obj P :=
    letI := tensorRightModObj P X
    ⟨P.X ⊗ X⟩
  map {P Q} f :=
    letI := tensorRightModObj P X
    letI := tensorRightModObj Q X
    homMk (M := ⟨P.X ⊗ X⟩) (N := ⟨Q.X ⊗ X⟩) (f.hom ▷ X) (by
      change ((α_ A P.X X).inv ≫ act P.X ▷ X) ≫ f.hom ▷ X =
        A ◁ f.hom ▷ X ≫ (α_ A Q.X X).inv ≫ act Q.X ▷ X
      rw [Category.assoc, ← comp_whiskerRight, act_hom, comp_whiskerRight,
        associator_inv_naturality_middle_assoc])
  map_id _ := Mod.hom_ext _ _ (id_whiskerRight _ _)
  map_comp _ _ := Mod.hom_ext _ _ (comp_whiskerRight _ _ _)


variable (A) in
/-- The natural transformation `P ⊗ X ⟶ P ⊗ Y` induced by `g : X ⟶ Y`. -/
@[simps!]
def tensorRightMap {X Y : C} (g : X ⟶ Y) : tensorRight A X ⟶ tensorRight A Y where
  app P := homMk (M := (tensorRight A X).obj P) (N := (tensorRight A Y).obj P) (P.X ◁ g) (by
    change ((α_ A P.X X).inv ≫ act P.X ▷ X) ≫ P.X ◁ g =
      A ◁ P.X ◁ g ≫ (α_ A P.X Y).inv ≫ act P.X ▷ Y
    rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc])
  naturality _ _ f := Mod.hom_ext _ _ (whisker_exchange _ _).symm

end TensorRight

section TensorLeft

variable [BraidedCategory C] [IsCommMonObj A]

/-- The right action `P ⊗ A ⟶ P` of a commutative monoid on a module. -/
abbrev rightAct (P : Mod C A) : P.X ⊗ A ⟶ P.X :=
  (β_ P.X A).hom ≫ act P.X

/-- The left and right actions of a commutative monoid on a module commute. -/
lemma act_whiskerRight_rightAct (P : Mod C A) :
    act P.X ▷ A ≫ rightAct P = (α_ A P.X A).hom ≫ A ◁ rightAct P ≫ act P.X := by
  rw [BraidedCategory.braiding_naturality_left_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  have h := mul_act (A := A) P.X
  rw [← cancel_epi (α_ A A P.X).inv, Iso.inv_hom_id_assoc] at h
  rw [← h, BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]

variable (A) in
/-- The second morphism `P ⊗ (A ⊗ M) ⟶ P ⊗ M` of the coequalizer defining `P ⊗_A M`: the right
action of `A` on `P`. -/
@[simps!]
def tensorRightRightAct (X : C) : tensorRight A (A ⊗ X) ⟶ tensorRight A X where
  app P := homMk (M := (tensorRight A (A ⊗ X)).obj P) (N := (tensorRight A X).obj P)
    ((α_ P.X A X).inv ≫ rightAct P ▷ X) (by
      change ((α_ A P.X (A ⊗ X)).inv ≫ act P.X ▷ (A ⊗ X)) ≫ (α_ P.X A X).inv ≫
          rightAct P ▷ X =
        A ◁ ((α_ P.X A X).inv ≫ rightAct P ▷ X) ≫ (α_ A P.X X).inv ≫ act P.X ▷ X
      rw [Category.assoc, associator_inv_naturality_left_assoc, ← comp_whiskerRight,
        act_whiskerRight_rightAct]
      simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
      monoidal)
  naturality P Q f := Mod.hom_ext _ _ (by
    have key : f.hom ▷ A ≫ rightAct Q = rightAct P ≫ f.hom := by
      simp only [rightAct, BraidedCategory.braiding_naturality_left_assoc, Category.assoc,
        act_hom]
    change f.hom ▷ (A ⊗ X) ≫ (α_ Q.X A X).inv ≫ rightAct Q ▷ X =
      ((α_ P.X A X).inv ≫ rightAct P ▷ X) ≫ f.hom ▷ X
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, key, comp_whiskerRight,
      Category.assoc])

omit [BraidedCategory C] [IsCommMonObj A] in
@[reassoc]
lemma tensorRightMap_comp {X Y Z : C} (g : X ⟶ Y) (h : Y ⟶ Z) :
    tensorRightMap A (g ≫ h) = tensorRightMap A g ≫ tensorRightMap A h := by
  refine NatTrans.ext (funext fun P ↦ Mod.hom_ext _ _ ?_)
  exact MonoidalCategory.whiskerLeft_comp P.X g h

variable [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]

variable (A) in
/-- The parallel pair `P ⊗ (A ⊗ M) ⇉ P ⊗ M`, functorially in `P`. -/
noncomputable abbrev tensorLeftDiagram (M : Mod C A) :
    WalkingParallelPair ⥤ Mod C A ⥤ Mod C A :=
  parallelPair (tensorRightMap A (act M.X)) (tensorRightRightAct A M.X)

/-- The tensor product `P ⊗_A M` of `A`-modules over a commutative monoid, as a functor of `P`:
the coequalizer of `P ⊗ (A ⊗ M) ⇉ P ⊗ M`, the two maps being the actions of `A` on `M` and on
`P`. -/
noncomputable def tensorLeft (M : Mod C A) : Mod C A ⥤ Mod C A :=
  (tensorLeftDiagram A M).flip ⋙ colim

variable (A) in
/-- The morphism of parallel pairs induced by a morphism of modules `f : M ⟶ M'`. -/
noncomputable def tensorLeftDiagramMap {M M' : Mod C A} (f : M ⟶ M') :
    tensorLeftDiagram A M ⟶ tensorLeftDiagram A M' :=
  parallelPairHom _ _ _ _ (tensorRightMap A (A ◁ f.hom)) (tensorRightMap A f.hom)
    (by rw [← tensorRightMap_comp, ← tensorRightMap_comp, act_hom])
    (by
      refine NatTrans.ext (funext fun P ↦ Mod.hom_ext _ _ ?_)
      change ((α_ P.X A M.X).inv ≫ rightAct P ▷ M.X) ≫ P.X ◁ f.hom =
        P.X ◁ A ◁ f.hom ≫ ((α_ P.X A M'.X).inv ≫ rightAct P ▷ M'.X)
      rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc])

/-- The tensor product is functorial in the second variable. -/
noncomputable def tensorLeftMap {M M' : Mod C A} (f : M ⟶ M') : tensorLeft M ⟶ tensorLeft M' :=
  Functor.whiskerRight ((flipFunctor _ _ _).map (tensorLeftDiagramMap A f)) colim

omit [BraidedCategory C] [IsCommMonObj A] [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma tensorRightMap_id (X : C) : tensorRightMap A (𝟙 X) = 𝟙 _ :=
  NatTrans.ext (funext fun _ ↦ Mod.hom_ext _ _ (MonoidalCategory.whiskerLeft_id _ _))

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma tensorLeftDiagramMap_comp {M M' M'' : Mod C A} (f : M ⟶ M') (g : M' ⟶ M'') :
    tensorLeftDiagramMap A (f ≫ g) = tensorLeftDiagramMap A f ≫ tensorLeftDiagramMap A g := by
  ext j : 2
  cases j
  · exact (congrArg (tensorRightMap A) (MonoidalCategory.whiskerLeft_comp A _ _)).trans
      (tensorRightMap_comp _ _)
  · exact tensorRightMap_comp _ _

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma tensorLeftDiagramMap_id (M : Mod C A) : tensorLeftDiagramMap A (𝟙 M) = 𝟙 _ := by
  ext j : 2
  cases j
  · exact (congrArg (tensorRightMap A) (MonoidalCategory.whiskerLeft_id A _)).trans
      (tensorRightMap_id _)
  · exact tensorRightMap_id _

lemma tensorLeftMap_comp {M M' M'' : Mod C A} (f : M ⟶ M') (g : M' ⟶ M'') :
    tensorLeftMap (f ≫ g) = tensorLeftMap f ≫ tensorLeftMap g := by
  rw [tensorLeftMap, tensorLeftMap, tensorLeftMap, tensorLeftDiagramMap_comp, Functor.map_comp,
    Functor.whiskerRight_comp]

lemma tensorLeftMap_id (M : Mod C A) : tensorLeftMap (𝟙 M) = 𝟙 _ := by
  rw [tensorLeftMap, tensorLeftDiagramMap_id, CategoryTheory.Functor.map_id,
    Functor.whiskerRight_id']
  rfl

section Additive

variable [Preadditive C] [MonoidalPreadditive C]

/-- The tensor product `- ⊗_A M` is additive in `M`. -/
lemma tensorLeftMap_add {M M' : Mod C A} (f g : M ⟶ M') :
    tensorLeftMap (f + g) = tensorLeftMap f + tensorLeftMap g := by
  ext P : 2
  refine colimit.hom_ext fun j ↦ ?_
  simp only [tensorLeftMap, Functor.whiskerRight_app, colim_map, ι_colimMap, NatTrans.app_add,
    Preadditive.comp_add]
  cases j
  · ext
    change P.X ◁ A ◁ (f.hom + g.hom) ≫ _ = P.X ◁ A ◁ f.hom ≫ _ + P.X ◁ A ◁ g.hom ≫ _
    simp [MonoidalPreadditive.whiskerLeft_add]
  · ext
    change P.X ◁ (f.hom + g.hom) ≫ _ = P.X ◁ f.hom ≫ _ + P.X ◁ g.hom ≫ _
    simp [MonoidalPreadditive.whiskerLeft_add]

end Additive

/-- An isomorphism `M ≅ M'` induces `- ⊗_A M ≅ - ⊗_A M'`. -/
noncomputable def tensorLeftMapIso {M M' : Mod C A} (e : M ≅ M') :
    tensorLeft M ≅ tensorLeft M' where
  hom := tensorLeftMap e.hom
  inv := tensorLeftMap e.inv
  hom_inv_id := by
    rw [tensorLeftMap, tensorLeftMap, ← Functor.whiskerRight_comp, ← Functor.map_comp,
      ← tensorLeftDiagramMap_comp, e.hom_inv_id, tensorLeftDiagramMap_id, Functor.map_id,
      Functor.whiskerRight_id']
    rfl
  inv_hom_id := by
    rw [tensorLeftMap, tensorLeftMap, ← Functor.whiskerRight_comp, ← Functor.map_comp,
      ← tensorLeftDiagramMap_comp, e.inv_hom_id, tensorLeftDiagramMap_id, Functor.map_id,
      Functor.whiskerRight_id']
    rfl

end TensorLeft

section Hom

variable [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

attribute [local instance] Mod.isGrothendieckAbelian

instance (X : C) : PreservesColimitsOfSize.{v, v} (tensorRight A X) := by
  have : PreservesColimitsOfSize.{v, v} (tensorRight A X ⋙ forget A) :=
    inferInstanceAs (PreservesColimitsOfSize.{v, v} (forget A ⋙ MonoidalCategory.tensorRight X))
  exact preservesColimits_of_reflects_of_preserves _ (forget A)

instance (M : Mod C A) : PreservesColimitsOfSize.{v, v} (tensorLeft M) := by
  have : PreservesColimitsOfSize.{v, v} (tensorLeftDiagram A M).flip :=
    ⟨fun {J} _ ↦ preservesColimitsOfShape_of_evaluation _ _ fun k ↦ by
      cases k <;> exact inferInstanceAs (PreservesColimitsOfShape J (tensorRight A _))⟩
  exact inferInstanceAs (PreservesColimitsOfSize.{v, v} ((tensorLeftDiagram A M).flip ⋙ colim))

instance (M : Mod C A) : (tensorLeft M).IsLeftAdjoint :=
  isLeftAdjoint_of_preservesColimits_of_isSeparating (isSeparator_separator (Mod C A)) _

/-- The internal hom `Hom_A(M, -)` of modules over a commutative monoid: the right adjoint of
`- ⊗_A M`. -/
noncomputable def ihom (M : Mod C A) : Mod C A ⥤ Mod C A :=
  (tensorLeft M).rightAdjoint

/-- The adjunction `- ⊗_A M ⊣ Hom_A(M, -)`. -/
noncomputable def ihomAdjunction (M : Mod C A) : tensorLeft M ⊣ ihom M :=
  Adjunction.ofIsLeftAdjoint _

instance (M : Mod C A) : (ihom M).Additive :=
  have := (ihomAdjunction M).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- An isomorphism `M ≅ M'` induces `Hom_A(M', -) ≅ Hom_A(M, -)`. -/
noncomputable def ihomMapIso {M M' : Mod C A} (e : M ≅ M') : ihom M' ≅ ihom M :=
  conjugateIsoEquiv (ihomAdjunction M') (ihomAdjunction M) (tensorLeftMapIso e)

/-- The internal hom is contravariant in the first variable. -/
noncomputable def ihomMap {M M' : Mod C A} (f : M ⟶ M') : ihom M' ⟶ ihom M :=
  conjugateEquiv (ihomAdjunction M') (ihomAdjunction M) (tensorLeftMap f)


lemma ihomMap_add {M M' : Mod C A} (f g : M ⟶ M') : ihomMap (f + g) = ihomMap f + ihomMap g := by
  ext N
  simp [ihomMap, tensorLeftMap_add, Preadditive.add_comp, Preadditive.comp_add]

lemma ihomMap_comp {M M' M'' : Mod C A} (f : M ⟶ M') (g : M' ⟶ M'') :
    ihomMap (f ≫ g) = ihomMap g ≫ ihomMap f := by
  rw [ihomMap, ihomMap, ihomMap, conjugateEquiv_comp, tensorLeftMap_comp]

lemma ihomMap_id (M : Mod C A) : ihomMap (𝟙 M) = 𝟙 _ := by
  rw [ihomMap, tensorLeftMap_id, conjugateEquiv_id]

end Hom

section Functor

open Functor.LaxMonoidal

open scoped Obj

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  {G : C ⥤ D} [G.LaxMonoidal] [∀ X Y : C, IsIso (Functor.LaxMonoidal.μ G X Y)]
  (ρ : B ⟶ G.obj A) [IsMonHom ρ]

/-- The functor on modules induced by a lax monoidal functor `G : C ⥤ D` and a monoid morphism
`ρ : B ⟶ G A`. -/
noncomputable abbrev mapModComap : Mod C A ⥤ Mod D B :=
  G.mapMod A ⋙ comap ρ

/-- A lax monoidal functor with invertible tensor comparison commutes with `- ⊗ X`. -/
noncomputable def tensorRightCompMapModComapIso (X : C) :
    tensorRight A X ⋙ mapModComap ρ ≅ mapModComap ρ ⋙ tensorRight B (G.obj X) :=
  NatIso.ofComponents (fun P ↦ isoMk (M := (mapModComap ρ).obj ((tensorRight A X).obj P))
      (N := (tensorRight B (G.obj X)).obj ((mapModComap ρ).obj P))
      (asIso (Functor.LaxMonoidal.μ G P.X X)).symm (by
        change (ρ ▷ G.obj (P.X ⊗ X) ≫ Functor.LaxMonoidal.μ G A (P.X ⊗ X) ≫
            G.map ((α_ A P.X X).inv ≫ act P.X ▷ X)) ≫ inv (Functor.LaxMonoidal.μ G P.X X) =
          B ◁ inv (Functor.LaxMonoidal.μ G P.X X) ≫ (α_ B (G.obj P.X) (G.obj X)).inv ≫
            (ρ ▷ G.obj P.X ≫ Functor.LaxMonoidal.μ G A P.X ≫ G.map (act P.X)) ▷ G.obj X
        rw [← cancel_mono (Functor.LaxMonoidal.μ G P.X X)]
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, comp_whiskerRight,
          μ_natural_left, Functor.map_comp]
        rw [← associator_inv_naturality_left_assoc, ← associativity_inv_assoc,
          ← whisker_exchange_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id,
          MonoidalCategory.whiskerLeft_id, Category.id_comp]))
    fun f ↦ Mod.hom_ext _ _ (by
      change G.map (f.hom ▷ X) ≫ inv (Functor.LaxMonoidal.μ G _ X) =
        inv (Functor.LaxMonoidal.μ G _ X) ≫ G.map f.hom ▷ G.obj X
      rw [IsIso.comp_inv_eq, Category.assoc, μ_natural_left, IsIso.inv_hom_id_assoc])

variable [BraidedCategory C] [IsCommMonObj A] [BraidedCategory D] [IsCommMonObj B] [IsIso ρ]

/-- The isomorphism `G (A ⊗ M) ≅ B ⊗ G M`, from the inverses of `μ` and of `ρ`. -/
noncomputable def mapTensorIso (M : C) : G.obj (A ⊗ M) ≅ B ⊗ G.obj M :=
  (asIso (Functor.LaxMonoidal.μ G A M)).symm ≪≫ whiskerRightIso (asIso ρ).symm _

/-- The functor `- ⊗ X` on modules along an isomorphism `X ≅ Y`. -/
@[simps]
def tensorRightMapIso {X Y : C} (e : X ≅ Y) : tensorRight A X ≅ tensorRight A Y where
  hom := tensorRightMap A e.hom
  inv := tensorRightMap A e.inv
  hom_inv_id := by
    rw [← tensorRightMap_comp, e.hom_inv_id]
    exact NatTrans.ext (funext fun P ↦ Mod.hom_ext _ _ (MonoidalCategory.whiskerLeft_id _ _))
  inv_hom_id := by
    rw [← tensorRightMap_comp, e.inv_hom_id]
    exact NatTrans.ext (funext fun P ↦ Mod.hom_ext _ _ (MonoidalCategory.whiskerLeft_id _ _))

omit [BraidedCategory C] [IsCommMonObj A] [BraidedCategory D] [IsCommMonObj B] in
lemma map_tensorRightMap_act_comp (M P : Mod C A) :
    ((mapModComap ρ).map ((tensorRightMap A (act M.X)).app P) ≫
        ((tensorRightCompMapModComapIso ρ M.X).app P).hom).hom =
      (((tensorRightCompMapModComapIso ρ (A ⊗ M.X)).app P).hom ≫
        (tensorRightMap B (mapTensorIso ρ M.X).hom).app ((mapModComap ρ).obj P) ≫
        (tensorRightMap B (act ((mapModComap ρ).obj M).X)).app ((mapModComap ρ).obj P)).hom := by
  change G.map (P.X ◁ act M.X) ≫ inv (Functor.LaxMonoidal.μ G P.X M.X) =
    inv (Functor.LaxMonoidal.μ G P.X (A ⊗ M.X)) ≫ G.obj P.X ◁ (mapTensorIso ρ M.X).hom ≫
      G.obj P.X ◁ (ρ ▷ G.obj M.X ≫ Functor.LaxMonoidal.μ G A M.X ≫ G.map (act M.X))
  have h : (mapTensorIso ρ M.X).hom ≫ (ρ ▷ G.obj M.X ≫ Functor.LaxMonoidal.μ G A M.X ≫
      G.map (act M.X)) = G.map (act M.X) := by
    simp [mapTensorIso, ← comp_whiskerRight_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp, h, IsIso.comp_inv_eq, Category.assoc, μ_natural_right,
    IsIso.inv_hom_id_assoc]

lemma map_tensorRightRightAct_comp
    (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X) (M P : Mod C A) :
    ((mapModComap ρ).map ((tensorRightRightAct A M.X).app P) ≫
        ((tensorRightCompMapModComapIso ρ M.X).app P).hom).hom =
      (((tensorRightCompMapModComapIso ρ (A ⊗ M.X)).app P).hom ≫
        (tensorRightMap B (mapTensorIso ρ M.X).hom).app ((mapModComap ρ).obj P) ≫
        (tensorRightRightAct B ((mapModComap ρ).obj M).X).app ((mapModComap ρ).obj P)).hom := by
  change G.map ((α_ P.X A M.X).inv ≫ rightAct P ▷ M.X) ≫ inv (Functor.LaxMonoidal.μ G P.X M.X) =
    inv (Functor.LaxMonoidal.μ G P.X (A ⊗ M.X)) ≫ G.obj P.X ◁ (mapTensorIso ρ M.X).hom ≫
      (α_ (G.obj P.X) B (G.obj M.X)).inv ≫
        ((β_ (G.obj P.X) B).hom ≫ ρ ▷ G.obj P.X ≫ Functor.LaxMonoidal.μ G A P.X ≫
          G.map (act P.X)) ▷ G.obj M.X
  rw [IsIso.comp_inv_eq]
  simp only [mapTensorIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, whiskerRightIso_hom,
    MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc, Functor.map_comp,
    μ_natural_left]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc (inv ρ ▷ G.obj P.X), ← comp_whiskerRight (inv ρ) ρ,
    IsIso.inv_hom_id, id_whiskerRight, id_whiskerRight, Category.id_comp,
    ← comp_whiskerRight_assoc, ← hβ, comp_whiskerRight_assoc,
    μ_natural_left_assoc, ← associativity_inv_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    IsIso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp, IsIso.inv_hom_id_assoc]

variable [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]
  [HasColimitsOfShape WalkingParallelPair D]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft B)]
  (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)

/-- The parallel pairs defining `P ⊗_A M` are compatible with `G`. -/
noncomputable def tensorLeftDiagramCompIso (M : Mod C A) :
    (tensorLeftDiagram A M).flip ⋙ (Functor.whiskeringRight _ _ _).obj (mapModComap ρ) ≅
      mapModComap ρ ⋙ (tensorLeftDiagram B ((mapModComap ρ).obj M)).flip :=
  NatIso.ofComponents (fun P ↦ parallelPair.ext
      ((tensorRightCompMapModComapIso ρ (A ⊗ M.X)).app P ≪≫
        (tensorRightMapIso (mapTensorIso ρ M.X)).app ((mapModComap ρ).obj P))
      ((tensorRightCompMapModComapIso ρ M.X).app P)
      (Mod.hom_ext _ _ (by simpa using map_tensorRightMap_act_comp ρ M P))
      (Mod.hom_ext _ _ (by simpa using map_tensorRightRightAct_comp ρ hβ M P)))
    fun {P Q} f ↦ by
      ext j : 2
      cases j
      · have h₁ := (tensorRightCompMapModComapIso ρ (A ⊗ M.X)).hom.naturality f
        have h₂ := (tensorRightMapIso (A := B) (mapTensorIso ρ M.X)).hom.naturality
          ((mapModComap ρ).map f)
        simp only [Functor.comp_map] at h₁
        simp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.flip_obj_obj,
          Functor.comp_map, Functor.whiskeringRight_obj_map, NatTrans.comp_app,
          Functor.flip_map_app, Functor.whiskerRight_app, parallelPair.ext_hom_app,
          Iso.trans_hom, Iso.app_hom, Category.assoc, parallelPair_obj_zero]
        rw [reassoc_of% h₁]
        exact congrArg (_ ≫ ·) h₂
      · exact (tensorRightCompMapModComapIso ρ M.X).hom.naturality f

/-- **The tensor product of modules is compatible with `G`**: `G (P ⊗_A M) ≅ G P ⊗_A G M`. -/
noncomputable def tensorLeftCompMapModComapIso
    [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)] (M : Mod C A) :
    tensorLeft M ⋙ mapModComap ρ ≅ mapModComap ρ ⋙ tensorLeft ((mapModComap ρ).obj M) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tensorLeftDiagram A M).flip (preservesColimitNatIso _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tensorLeftDiagramCompIso ρ hβ M) colim ≪≫ Functor.associator _ _ _

end Functor

section HomFunctor

open scoped Obj

variable [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [BraidedCategory D] [IsCommMonObj B] [Abelian D] [MonoidalPreadditive D]
  [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)]
  {G : C ⥤ D} [G.LaxMonoidal] [∀ X Y : C, IsIso (Functor.LaxMonoidal.μ G X Y)]
  (ρ : B ⟶ G.obj A) [IsMonHom ρ] [IsIso ρ]
  (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)
  [(mapModComap ρ).IsEquivalence]

/-- **The internal hom of modules is compatible with `G`**:
`G Hom_A(M, N) ≅ Hom_A(G M, G N)`, naturally in `N`. -/
noncomputable def mapModComapCompIhomIso (M : Mod C A) :
    mapModComap ρ ⋙ ihom ((mapModComap ρ).obj M) ≅ ihom M ⋙ mapModComap ρ :=
  let E := (mapModComap ρ).asEquivalence
  let adj := (E.symm.toAdjunction.comp (ihomAdjunction M)).comp E.toAdjunction
  let i : E.inverse ⋙ tensorLeft M ⋙ E.functor ≅ tensorLeft ((mapModComap ρ).obj M) :=
    Functor.isoWhiskerLeft E.inverse (tensorLeftCompMapModComapIso ρ hβ M) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.counitIso _ ≪≫
      Functor.leftUnitor _
  let j : ihom ((mapModComap ρ).obj M) ≅ E.inverse ⋙ ihom M ⋙ E.functor :=
    (ihomAdjunction ((mapModComap ρ).obj M)).rightAdjointUniq
      ((adj.ofNatIsoLeft (Functor.associator _ _ _)).ofNatIsoLeft i)
  Functor.isoWhiskerLeft E.functor j ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight E.unitIso.symm _ ≪≫ Functor.leftUnitor _

end HomFunctor

end CategoryTheory.Mod
