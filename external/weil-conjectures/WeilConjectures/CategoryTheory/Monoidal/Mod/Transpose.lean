/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation

/-!
# Transposition of morphisms into internal homs of modules

Let `A` be a commutative monoid in a symmetric monoidal abelian category `C`. For `A`-modules
`P`, `M`, `N`, a morphism `v : P ⟶ Hom_A(M, N)` is determined by the morphism
`P ⊗ M ⟶ N` of underlying objects obtained by evaluation
(`CategoryTheory.Mod.uncurryHom`), and the morphisms arising this way are exactly the
`A`-bilinear ones (`CategoryTheory.Mod.IsBilinear`): `A`-linear in `P` and coequalizing the two
actions of `A`. Precomposing with the symmetry `M ⊗ P ≅ P ⊗ M` preserves bilinearity, which gives
the transposition `Hom(P, Hom_A(M, N)) ≃ Hom(M, Hom_A(P, N))`
(`CategoryTheory.Mod.transpose`): `v ↦ (m ↦ (p ↦ v(p)(m)))`. It is involutive and natural in all
three variables.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

section Bilinear

variable [BraidedCategory C]

/-- A morphism `u : P ⊗ M ⟶ N` of underlying objects of `A`-modules is *bilinear* if it is
`A`-linear in `P` and coequalizes the actions of `A` on `P` and on `M`. -/
structure IsBilinear {P M N : Mod C A} (u : P.X ⊗ M.X ⟶ N.X) : Prop where
  linear : (α_ A P.X M.X).inv ≫ act P.X ▷ M.X ≫ u = A ◁ u ≫ act N.X
  balanced : P.X ◁ act M.X ≫ u = (α_ P.X A M.X).inv ≫ rightAct P ▷ M.X ≫ u

variable {P P' M M' N N' : Mod C A}

/-- Bilinearity is preserved by postcomposition with a linear map. -/
lemma IsBilinear.comp {u : P.X ⊗ M.X ⟶ N.X} (hu : IsBilinear (P := P) (M := M) u)
    (f : N ⟶ N') : IsBilinear (P := P) (M := M) (u ≫ f.hom) where
  linear := by
    rw [reassoc_of% hu.linear, act_hom, MonoidalCategory.whiskerLeft_comp_assoc]
  balanced := by
    rw [reassoc_of% hu.balanced]

/-- Bilinearity is preserved by precomposition with a linear map in the first variable. -/
lemma IsBilinear.whiskerRight {u : P.X ⊗ M.X ⟶ N.X} (hu : IsBilinear (P := P) (M := M) u)
    (g : P' ⟶ P) : IsBilinear (P := P') (M := M) (g.hom ▷ M.X ≫ u) where
  linear := by
    rw [← comp_whiskerRight_assoc, act_hom, comp_whiskerRight_assoc,
      ← associator_inv_naturality_middle_assoc, hu.linear, MonoidalCategory.whiskerLeft_comp_assoc]
  balanced := by
    have key : g.hom ▷ A ≫ rightAct P = rightAct P' ≫ g.hom := by
      simp only [rightAct, BraidedCategory.braiding_naturality_left_assoc, Category.assoc, act_hom]
    rw [whisker_exchange_assoc, hu.balanced, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, key, comp_whiskerRight_assoc]

/-- Bilinearity is preserved by precomposition with a linear map in the second variable. -/
lemma IsBilinear.whiskerLeft {u : P.X ⊗ M.X ⟶ N.X} (hu : IsBilinear (P := P) (M := M) u)
    (g : M' ⟶ M) : IsBilinear (P := P) (M := M') (P.X ◁ g.hom ≫ u) where
  linear := by
    rw [← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc, hu.linear,
      MonoidalCategory.whiskerLeft_comp_assoc]
  balanced := by
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, act_hom, MonoidalCategory.whiskerLeft_comp_assoc,
      hu.balanced, associator_inv_naturality_right_assoc, whisker_exchange_assoc]

end Bilinear

section Symmetric

variable [SymmetricCategory C] {P M N : Mod C A}

/-- The braiding identity `(A ⊗ M) ⊗ P ≅ A ⊗ (P ⊗ M)` used to transpose bilinear maps. -/
@[reassoc]
lemma braiding_tensor_left_comp_braiding_whiskerRight_eq (X Y Z : C) :
    (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv ≫ (β_ Z X).hom ▷ Y ≫ (α_ X Z Y).hom =
      (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).hom := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

/-- Precomposing a bilinear map `P ⊗ M ⟶ N` with the symmetry `M ⊗ P ≅ P ⊗ M` gives a bilinear
map `M ⊗ P ⟶ N`. -/
lemma IsBilinear.braiding {u : P.X ⊗ M.X ⟶ N.X} (hu : IsBilinear (P := P) (M := M) u) :
    IsBilinear (P := M) (M := P) ((β_ M.X P.X).hom ≫ u) := by
  -- `u ∘ (P ◁ act_M) = α ≫ A ◁ u ≫ act_N` up to the braidings
  have key : P.X ◁ act M.X ≫ u =
      (α_ P.X A M.X).inv ≫ (β_ P.X A).hom ▷ M.X ≫ (α_ A P.X M.X).hom ≫ A ◁ u ≫ act N.X := by
    rw [hu.balanced, ← hu.linear]
    simp only [rightAct, comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]
  have key' : act M.X ▷ P.X ≫ (β_ M.X P.X).hom ≫ u =
      (α_ A M.X P.X).hom ≫ A ◁ (β_ M.X P.X).hom ≫ A ◁ u ≫ act N.X := by
    rw [BraidedCategory.braiding_naturality_left_assoc, key,
      ← braiding_tensor_left_comp_braiding_whiskerRight_eq_assoc]
  have hlin : act P.X ▷ M.X ≫ u = (α_ A P.X M.X).hom ≫ A ◁ u ≫ act N.X := by
    rw [← hu.linear, Iso.hom_inv_id_assoc]
  refine ⟨?_, ?_⟩
  · rw [key', Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  · rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc, hlin]
    simp only [rightAct, comp_whiskerRight, Category.assoc]
    rw [key', BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Symmetric

section Hom

variable [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  {P P' M M' N N' : Mod C A}

variable (P M) in
/-- The quotient map `P ⊗ M ⟶ P ⊗_A M` is bilinear. -/
lemma isBilinear_tensorπ : IsBilinear (P := P) (M := M) (tensorπ P M) where
  linear := (Category.assoc _ _ _).symm.trans
    (act_hom (colimit.ι ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPair.one))
  balanced := by
    have h := congrArg Mod.Hom.hom
      ((colimit.w ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPairHom.left).trans
        (colimit.w ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPairHom.right).symm)
    simp only [Mod.comp_hom'] at h
    exact h.trans (Category.assoc _ _ _)

/-- Two morphisms out of `P ⊗_A M` agreeing on `P ⊗ M` are equal. -/
lemma tensorLeft_obj_hom_ext {f g : (tensorLeft M).obj P ⟶ N}
    (h : tensorπ P M ≫ f.hom = tensorπ P M ≫ g.hom) : f = g := by
  have h₁ : colimit.ι ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPair.one ≫ f =
      colimit.ι ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPair.one ≫ g :=
    Mod.hom_ext _ _ h
  refine colimit.hom_ext fun j ↦ ?_
  cases j
  · rw [← colimit.w ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPairHom.left,
      Category.assoc, Category.assoc, h₁]
  · exact h₁

/-- A bilinear map `P ⊗ M ⟶ N`, as a morphism of `A`-modules `P ⊗ M ⟶ N`, `A` acting on `P`. -/
noncomputable def IsBilinear.tensorRightHom {u : P.X ⊗ M.X ⟶ N.X}
    (hu : IsBilinear (P := P) (M := M) u) : (tensorRight A M.X).obj P ⟶ N :=
  homMk (M := (tensorRight A M.X).obj P) u ((Category.assoc _ _ _).trans hu.linear)

omit [Abelian C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)] in
lemma IsBilinear.tensorRightHom_coequalizes {u : P.X ⊗ M.X ⟶ N.X}
    (hu : IsBilinear (P := P) (M := M) u) :
    (tensorRightMap A (act M.X)).app P ≫ hu.tensorRightHom =
      (tensorRightRightAct A M.X).app P ≫ hu.tensorRightHom :=
  Mod.hom_ext _ _ (by
    simp only [Mod.comp_hom', tensorRightMap_app_hom, tensorRightRightAct_app_hom,
      IsBilinear.tensorRightHom, homMk_hom, Category.assoc]
    exact hu.balanced.trans (by simp only [rightAct, comp_whiskerRight, Category.assoc]))

/-- The morphism `P ⊗_A M ⟶ N` induced by a bilinear map `P ⊗ M ⟶ N`. -/
noncomputable def tensorDesc (u : P.X ⊗ M.X ⟶ N.X) (hu : IsBilinear (P := P) (M := M) u) :
    (tensorLeft M).obj P ⟶ N :=
  colimit.desc ((tensorLeftDiagram A M).flip.obj P)
    { pt := N
      ι :=
        { app j := match j with
            | .zero => (tensorRightMap A (act M.X)).app P ≫ hu.tensorRightHom
            | .one => hu.tensorRightHom
          naturality := by
            rintro _ _ (_ | _ | _)
            · exact (Category.comp_id _).symm
            · exact hu.tensorRightHom_coequalizes.symm.trans (Category.comp_id _).symm
            · simp } }

lemma tensorπ_tensorDesc (u : P.X ⊗ M.X ⟶ N.X) (hu : IsBilinear (P := P) (M := M) u) :
    tensorπ P M ≫ (tensorDesc u hu).hom = u := by
  rw [tensorπ, ← Mod.comp_hom', tensorDesc, colimit.ι_desc]
  rfl

variable [MonoidalPreadditive C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

/-- The morphism `P ⊗ M ⟶ N` of underlying objects corresponding to `v : P ⟶ Hom_A(M, N)`:
`p ⊗ m ↦ v(p)(m)`. -/
noncomputable def uncurryHom (v : P ⟶ (ihom M).obj N) : P.X ⊗ M.X ⟶ N.X :=
  v.hom ▷ M.X ≫ evaluation M N

lemma uncurryHom_eq (v : P ⟶ (ihom M).obj N) :
    uncurryHom v = tensorπ P M ≫ (((ihomAdjunction M).homEquiv P N).symm v).hom := by
  rw [Adjunction.homEquiv_counit, Mod.comp_hom', tensorπ_map_assoc, uncurryHom, evaluation]

lemma isBilinear_uncurryHom (v : P ⟶ (ihom M).obj N) :
    IsBilinear (P := P) (M := M) (uncurryHom v) := by
  rw [uncurryHom_eq]
  exact (isBilinear_tensorπ P M).comp _

lemma uncurryHom_injective :
    Function.Injective (uncurryHom (P := P) (M := M) (N := N)) := by
  intro v w h
  rw [uncurryHom_eq, uncurryHom_eq] at h
  exact ((ihomAdjunction M).homEquiv P N).symm.injective (tensorLeft_obj_hom_ext h)

/-- The morphism `P ⟶ Hom_A(M, N)` corresponding to a bilinear map `P ⊗ M ⟶ N`. -/
noncomputable def curryHom (u : P.X ⊗ M.X ⟶ N.X) (hu : IsBilinear (P := P) (M := M) u) :
    P ⟶ (ihom M).obj N :=
  (ihomAdjunction M).homEquiv P N (tensorDesc u hu)

@[simp]
lemma uncurryHom_curryHom (u : P.X ⊗ M.X ⟶ N.X) (hu : IsBilinear (P := P) (M := M) u) :
    uncurryHom (curryHom u hu) = u := by
  rw [uncurryHom_eq, curryHom, Equiv.symm_apply_apply, tensorπ_tensorDesc]

lemma uncurryHom_comp (g : P' ⟶ P) (v : P ⟶ (ihom M).obj N) :
    uncurryHom (g ≫ v) = g.hom ▷ M.X ≫ uncurryHom v := by
  rw [uncurryHom, uncurryHom, Mod.comp_hom', comp_whiskerRight_assoc]

lemma uncurryHom_comp_ihomMap (v : P ⟶ (ihom M).obj N) (h : M' ⟶ M) :
    uncurryHom (v ≫ (ihomMap h).app N) = P.X ◁ h.hom ≫ uncurryHom v := by
  rw [uncurryHom, uncurryHom, Mod.comp_hom', comp_whiskerRight_assoc, evaluation_ihomMap,
    whisker_exchange_assoc]

lemma uncurryHom_comp_ihom_map (v : P ⟶ (ihom M).obj N) (f : N ⟶ N') :
    uncurryHom (v ≫ (ihom M).map f) = uncurryHom v ≫ f.hom := by
  rw [uncurryHom, uncurryHom, Mod.comp_hom', comp_whiskerRight_assoc, evaluation_naturality,
    Category.assoc]

lemma uncurryHom_zero : uncurryHom (0 : P ⟶ (ihom M).obj N) = 0 := by
  rw [uncurryHom, Mod.zero_hom, MonoidalPreadditive.zero_whiskerRight, zero_comp]

/-- **Transposition**: the morphism `M ⟶ Hom_A(P, N)`, `m ↦ (p ↦ v(p)(m))`, transposed to
`v : P ⟶ Hom_A(M, N)`. -/
noncomputable def transpose (v : P ⟶ (ihom M).obj N) : M ⟶ (ihom P).obj N :=
  curryHom ((β_ M.X P.X).hom ≫ uncurryHom v) (isBilinear_uncurryHom v).braiding

@[simp]
lemma uncurryHom_transpose (v : P ⟶ (ihom M).obj N) :
    uncurryHom (transpose v) = (β_ M.X P.X).hom ≫ uncurryHom v :=
  uncurryHom_curryHom _ _

@[simp]
lemma transpose_transpose (v : P ⟶ (ihom M).obj N) : transpose (transpose v) = v :=
  uncurryHom_injective (by
    rw [uncurryHom_transpose, uncurryHom_transpose, SymmetricCategory.symmetry_assoc])

/-- Transposition as an equivalence `Hom(P, Hom_A(M, N)) ≃ Hom(M, Hom_A(P, N))`. -/
noncomputable def transposeEquiv : (P ⟶ (ihom M).obj N) ≃ (M ⟶ (ihom P).obj N) where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose

/-- Transposition is natural in the first variable. -/
lemma transpose_comp (g : P' ⟶ P) (v : P ⟶ (ihom M).obj N) :
    transpose (g ≫ v) = transpose v ≫ (ihomMap g).app N :=
  uncurryHom_injective (by
    rw [uncurryHom_transpose, uncurryHom_comp_ihomMap, uncurryHom_transpose, uncurryHom_comp,
      BraidedCategory.braiding_naturality_right_assoc])

/-- Transposition is natural in the second variable. -/
lemma transpose_comp_ihomMap (v : P ⟶ (ihom M).obj N) (h : M' ⟶ M) :
    transpose (v ≫ (ihomMap h).app N) = h ≫ transpose v :=
  uncurryHom_injective (by
    rw [uncurryHom_transpose, uncurryHom_comp_ihomMap, uncurryHom_comp, uncurryHom_transpose,
      BraidedCategory.braiding_naturality_left_assoc])

/-- Transposition is natural in the target. -/
lemma transpose_comp_ihom_map (v : P ⟶ (ihom M).obj N) (f : N ⟶ N') :
    transpose (v ≫ (ihom M).map f) = transpose v ≫ (ihom P).map f :=
  uncurryHom_injective (by
    rw [uncurryHom_transpose, uncurryHom_comp_ihom_map, uncurryHom_comp_ihom_map,
      uncurryHom_transpose, Category.assoc])

@[simp]
lemma transpose_zero : transpose (0 : P ⟶ (ihom M).obj N) = 0 :=
  uncurryHom_injective (by rw [uncurryHom_transpose, uncurryHom_zero, uncurryHom_zero, comp_zero])

@[simp]
lemma transpose_eq_zero_iff (v : P ⟶ (ihom M).obj N) : transpose v = 0 ↔ v = 0 :=
  ⟨fun h ↦ by rw [← transpose_transpose v, h, transpose_zero], fun h ↦ by rw [h, transpose_zero]⟩

end Hom

end CategoryTheory.Mod
