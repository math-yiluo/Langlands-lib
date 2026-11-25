/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor

/-!
# The evaluation pairing of the internal hom of modules

For modules `M`, `N` over a commutative monoid `A`, the evaluation `Hom_A(M, N) ⊗_A M ⟶ N`
(the counit of `- ⊗_A M ⊣ Hom_A(M, -)`) precomposed with the quotient map
`Hom_A(M, N) ⊗ M ⟶ Hom_A(M, N) ⊗_A M` is a morphism `Hom_A(M, N) ⊗ M ⟶ N` of the underlying
objects, `CategoryTheory.Mod.evaluation`. It is natural in `N` and dinatural in `M`.

A lax monoidal functor `G` with invertible tensor comparison, inducing an equivalence of module
categories, is compatible with the evaluations through the comparison
`G Hom_A(M, N) ≅ Hom_A(G M, G N)` of `CategoryTheory.Mod.mapModComapCompIhomIso`
(`CategoryTheory.Mod.μ_comp_map_evaluation`).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

section TensorLeft

variable [BraidedCategory C] [IsCommMonObj A] [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]

/-- The quotient map `P ⊗ M ⟶ P ⊗_A M` of the underlying objects. -/
noncomputable def tensorπ (P M : Mod C A) : P.X ⊗ M.X ⟶ ((tensorLeft M).obj P).X :=
  (colimit.ι ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPair.one).hom

@[reassoc]
lemma tensorπ_map (M : Mod C A) {P P' : Mod C A} (f : P ⟶ P') :
    tensorπ P M ≫ ((tensorLeft M).map f).hom = f.hom ▷ M.X ≫ tensorπ P' M := by
  have := colimit.ι_map ((tensorLeftDiagram A M).flip.map f) WalkingParallelPair.one
  exact congrArg Mod.Hom.hom this

@[reassoc]
lemma tensorπ_tensorLeftMap (P : Mod C A) {M M' : Mod C A} (g : M ⟶ M') :
    tensorπ P M ≫ ((tensorLeftMap g).app P).hom = P.X ◁ g.hom ≫ tensorπ P M' := by
  have := colimit.ι_map (((flipFunctor _ _ _).map (tensorLeftDiagramMap A g)).app P)
    WalkingParallelPair.one
  exact congrArg Mod.Hom.hom this

end TensorLeft

section Hom

variable [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

/-- The evaluation `Hom_A(M, N) ⊗ M ⟶ N` on the underlying objects. -/
noncomputable def evaluation (M N : Mod C A) : ((ihom M).obj N).X ⊗ M.X ⟶ N.X :=
  tensorπ _ M ≫ ((ihomAdjunction M).counit.app N).hom

/-- The evaluation is natural in the target. -/
@[reassoc]
lemma evaluation_naturality (M : Mod C A) {N N' : Mod C A} (f : N ⟶ N') :
    ((ihom M).map f).hom ▷ M.X ≫ evaluation M N' = evaluation M N ≫ f.hom := by
  rw [evaluation, ← tensorπ_map_assoc, ← Mod.comp_hom']
  erw [(ihomAdjunction M).counit_naturality]
  rw [Mod.comp_hom', evaluation, Category.assoc]

/-- The evaluation is dinatural in the source. -/
@[reassoc]
lemma evaluation_ihomMap {M M' : Mod C A} (g : M ⟶ M') (N : Mod C A) :
    ((ihomMap g).app N).hom ▷ M.X ≫ evaluation M N =
      ((ihom M').obj N).X ◁ g.hom ≫ evaluation M' N := by
  rw [evaluation, ← tensorπ_map_assoc, evaluation, ← tensorπ_tensorLeftMap_assoc,
    ← Mod.comp_hom', ← Mod.comp_hom', ihomMap, conjugateEquiv_counit]

end Hom

end CategoryTheory.Mod

namespace CategoryTheory.Mod

section HomFunctor

open scoped Obj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
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

omit [MonoidalPreadditive C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  [MonoidalPreadditive D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)] in
/-- The quotient map `P ⊗ M ⟶ P ⊗_A M` is compatible with `G`. -/
@[reassoc]
lemma map_tensorπ_comp_tensorLeftCompMapModComapIso_hom
    [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)] (P M : Mod C A) :
    G.map (tensorπ P M) ≫ ((tensorLeftCompMapModComapIso ρ hβ M).hom.app P).hom =
      inv (Functor.LaxMonoidal.μ G P.X M.X) ≫
        tensorπ ((mapModComap ρ).obj P) ((mapModComap ρ).obj M) := by
  have h : (mapModComap ρ).map (colimit.ι ((tensorLeftDiagram A M).flip.obj P)
      WalkingParallelPair.one) ≫ (tensorLeftCompMapModComapIso ρ hβ M).hom.app P =
        (tensorRightCompMapModComapIso ρ M.X).hom.app P ≫
          colimit.ι ((tensorLeftDiagram B ((mapModComap ρ).obj M)).flip.obj
            ((mapModComap ρ).obj P)) WalkingParallelPair.one := by
    simp only [tensorLeftCompMapModComapIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, preservesColimitNatIso_hom_app, Iso.symm_hom]
    erw [Category.id_comp, ι_preservesColimitIso_hom_assoc, Category.id_comp, colim_map,
      ι_colimMap_assoc, Category.comp_id]
    rfl
  exact congrArg Mod.Hom.hom h

variable [(mapModComap ρ).IsEquivalence]

/-- The comparison `Hom_B(G M, G N) ≅ G Hom_A(M, N)` is compatible with the evaluations. -/
lemma mapModComapCompIhomIso_inv_counit (M N : Mod C A) :
    (tensorLeft ((mapModComap ρ).obj M)).map ((mapModComapCompIhomIso ρ hβ M).inv.app N) ≫
        (ihomAdjunction _).counit.app _ =
      (tensorLeftCompMapModComapIso ρ hβ M).inv.app ((ihom M).obj N) ≫
        (mapModComap ρ).map ((ihomAdjunction M).counit.app N) := by
  simp only [mapModComapCompIhomIso, Iso.trans_inv, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Iso.symm_inv,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.id_comp, Functor.map_comp, Category.assoc, Adjunction.rightAdjointUniq_inv_app]
  erw [Adjunction.rightAdjointUniq_hom_app_counit]
  simp only [Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  have e₁ (X : Mod C A) : (mapModComap ρ).asEquivalence.symm.toAdjunction.counit.app X =
      (mapModComap ρ).asEquivalence.unitInv.app X := rfl
  have e₂ (Y : Mod D B) : (mapModComap ρ).asEquivalence.toAdjunction.counit.app Y =
      (mapModComap ρ).asEquivalence.counit.app Y := rfl
  have e₃ (X : Mod C A) : (mapModComap ρ).asEquivalence.counitIso.inv.app
      ((mapModComap ρ).asEquivalence.functor.obj X) =
        (mapModComap ρ).asEquivalence.functor.map
          ((mapModComap ρ).asEquivalence.unitIso.hom.app X) :=
    Equivalence.counitInv_app_functor _ X
  have nτ := (tensorLeftCompMapModComapIso ρ hβ M).inv.naturality
  simp only [Functor.comp_map, Functor.comp_obj] at nτ
  simp only [Functor.comp_obj, Functor.comp_map, Category.id_comp, e₁, e₂, e₃,
    Equivalence.counit_app_functor]
  erw [Functor.map_id, Category.id_comp, ← Functor.map_comp_assoc, ← Functor.map_comp,
    reassoc_of% nτ, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  erw [← Functor.map_comp]
  congr 2
  have hu (Z : Mod C A) {W : Mod C A} (h : (tensorLeft M).obj Z ⟶ W) :
      (tensorLeft M).map ((mapModComap ρ).asEquivalence.unitIso.hom.app Z) ≫
        (tensorLeft M).map ((mapModComap ρ).asEquivalence.unitInv.app Z) ≫ h = h := by
    rw [← Functor.map_comp_assoc]
    erw [Iso.hom_inv_id_app]
    rw [Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc, hu]
  erw [(ihomAdjunction M).counit_naturality_assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- The evaluations of `M` and of `G M` are compatible with `G`, through the comparison
`G Hom_A(M, N) ≅ Hom_B(G M, G N)`. -/
lemma μ_comp_map_evaluation (M N : Mod C A) :
    Functor.LaxMonoidal.μ G ((ihom M).obj N).X M.X ≫ G.map (evaluation M N) =
      ((mapModComapCompIhomIso ρ hβ M).inv.app N).hom ▷ ((mapModComap ρ).obj M).X ≫
        evaluation ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) := by
  have h₁ := map_tensorπ_comp_tensorLeftCompMapModComapIso_hom ρ hβ ((ihom M).obj N) M
  have h₂ : tensorπ ((mapModComap ρ).obj ((ihom M).obj N)) ((mapModComap ρ).obj M) ≫
      ((tensorLeftCompMapModComapIso ρ hβ M).inv.app ((ihom M).obj N)).hom =
        Functor.LaxMonoidal.μ G _ _ ≫ G.map (tensorπ ((ihom M).obj N) M) := by
    have h₃ : tensorπ ((mapModComap ρ).obj ((ihom M).obj N)) ((mapModComap ρ).obj M) =
        Functor.LaxMonoidal.μ G _ _ ≫ G.map (tensorπ ((ihom M).obj N) M) ≫
          ((tensorLeftCompMapModComapIso ρ hβ M).hom.app ((ihom M).obj N)).hom := by
      erw [h₁, IsIso.hom_inv_id_assoc]
    erw [h₃, Category.assoc, Category.assoc, ← Mod.comp_hom', Iso.hom_inv_id_app, Mod.id_hom',
      Category.comp_id]
  have key : ((mapModComapCompIhomIso ρ hβ M).inv.app N).hom ▷ ((mapModComap ρ).obj M).X ≫
      evaluation ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) =
        tensorπ ((mapModComap ρ).obj ((ihom M).obj N)) ((mapModComap ρ).obj M) ≫
          ((tensorLeftCompMapModComapIso ρ hβ M).inv.app ((ihom M).obj N)).hom ≫
            ((mapModComap ρ).map ((ihomAdjunction M).counit.app N)).hom := by
    rw [evaluation]
    erw [← tensorπ_map_assoc, ← Mod.comp_hom', mapModComapCompIhomIso_inv_counit]
    rfl
  refine Eq.trans ?_ key.symm
  rw [← Category.assoc, h₂, evaluation, Functor.map_comp, Category.assoc]
  rfl

end HomFunctor

end CategoryTheory.Mod
