/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization

/-! # The global-section augmentation as a cochain map
Source: Stacks Project, Tag 01EQ, the augmented double-complex construction.
(blueprint: lem-pbc-etale-additive-cech-alpha-map) -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def rowRestriction {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :=
  Pi.lift (fun y : Fin 1 → ι ↦ (I.cocomplex.X n).obj.map
    (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι
      (Category.comp_id _) :
      (additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)) ⟶
        Scheme.Etale.mk (𝟙 X)).op)

private lemma rowRestriction_horizontal {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    rowRestriction U I n ≫
      ((cechComplexFunctor U).obj ((additiveCechOpenInclusion X).op ⋙
        (I.cocomplex.X n).obj)).d 0 1 = 0 := by
  apply Pi.hom_ext
  intro y
  rw [Category.assoc, zero_comp]
  change rowRestriction U I n ≫
    ((cechComplexFunctor U).obj ((additiveCechOpenInclusion X).op ⋙
      (I.cocomplex.X n).obj)).d 0 1 ≫
    TopCat.Presheaf.cechComplexFunctorπ U
      ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X n).obj) 1 y = 0
  rw [TopCat.Presheaf.cechComplexFunctor_d_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
  have hh (j : Fin 2) : rowRestriction U I n ≫
      TopCat.Presheaf.cechComplexFunctorπ U
        ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X n).obj) 0
          (y ∘ j.succAbove) ≫
        ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X n).obj).map
          (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (j.succAbove l)).op =
      (I.cocomplex.X n).obj.map
        (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι
          (Category.comp_id _) :
          (additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)) ⟶
            Scheme.Etale.mk (𝟙 X)).op := by
    rw [← Category.assoc]
    erw [Pi.lift_comp_π]
    dsimp only [Functor.comp_map, Functor.op_map]
    rw [← Functor.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    exact (MorphismProperty.Over.mkIdTerminal @Etale X).hom_ext _ _
  simp_rw [hh]
  simp [Fin.sum_univ_two]

private lemma rowRestriction_vertical {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) (n m : ℕ) :
    rowRestriction U I n ≫
      ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).X 0).d
        n m = (additiveCechGlobal I).d n m ≫ rowRestriction U I m := by
  apply Pi.hom_ext
  intro y
  change rowRestriction U I n ≫
    Limits.Pi.map (fun y : Fin 1 → ι ↦ (I.cocomplex.d n m).hom.app
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))) ≫
      Pi.π _ y = ((I.cocomplex.d n m).hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
        rowRestriction U I m) ≫ Pi.π _ y
  rw [Category.assoc]
  erw [Pi.map_π]
  rw [← Category.assoc]
  erw [Pi.lift_comp_π]
  erw [Pi.lift_comp_π]
  exact (I.cocomplex.d n m).hom.naturality _

/-- Restriction into the degree-zero Čech column is a cochain map for any open family.
Source: Stacks Project, Tag 01EQ, proof of the augmented double-complex lemma.
(blueprint: lem-pbc-etale-additive-cech-alpha-map)

Proof: Let a_n be restriction from the terminal étale object to every single open.
The horizontal differential of a_n is zero, since on a two-entry tuple the two
restrictions coincide and have opposite signs. The vertical differential commutes
with a_n by naturality of the resolution differential. Include this column in the
total complex. Its vertical sign is positive in Čech degree zero, so these two
identities give the cochain-map equation. No covering or affine assumption enters;
empty families give zero restrictions, and the degree-zero equation is the same.
-/
theorem exists_additiveCech_alpha_map {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) :
    ∃ a : additiveCechGlobal I ⟶ additiveCechTotal U I,
      ∀ n, a.f n = additiveCechAlpha U I n := by
  let K := etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I
  refine ⟨{ f := additiveCechAlpha U I, comm' := ?_ }, fun _ ↦ rfl⟩
  intro n m h
  have hm : n + 1 = m := h
  subst m
  symm
  change (additiveCechGlobal I).d n (n + 1) ≫ additiveCechAlpha U I (n + 1) =
    additiveCechAlpha U I n ≫ (K.total (.up ℕ)).d n (n + 1)
  unfold additiveCechAlpha
  change (additiveCechGlobal I).d n (n + 1) ≫
      rowRestriction U I (n + 1) ≫ K.ιTotal (.up ℕ) 0 (n + 1) (n + 1) _ =
    rowRestriction U I n ≫ K.ιTotal (.up ℕ) 0 n n _ ≫ (K.total (.up ℕ)).d n (n + 1)
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    K.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1) n (n + 1) (by simp [Nat.add_comm]),
    K.d₂_eq (.up ℕ) 0 (by simp : (ComplexShape.up ℕ).Rel n (n + 1))
      (n + 1) (by simp)]
  have hsign₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, n) = 1 := rfl
  have hsign₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, n) = 1 := by
    change (ComplexShape.up ℕ).ε 0 = 1
    simp
  rw [hsign₁, hsign₂, one_smul, one_smul, Preadditive.comp_add,
    ← Category.assoc]
  have hz : rowRestriction U I n ≫ (K.d 0 1).f n = 0 :=
    rowRestriction_horizontal U I n
  rw [reassoc_of% hz, zero_comp, zero_add]
  rw [reassoc_of% rowRestriction_vertical U I n (n + 1)]
  rw [Category.assoc]

end AlgebraicGeometry.Scheme.Modules
