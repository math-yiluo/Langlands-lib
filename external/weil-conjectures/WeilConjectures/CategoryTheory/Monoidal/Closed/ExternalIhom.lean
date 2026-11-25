/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# The external internal-hom map

Let `F₁ : D₁ ⥤ C` and `F₂ : D₂ ⥤ C` be lax monoidal functors into a braided monoidal closed
category. The *external internal-hom map*
(`CategoryTheory.MonoidalClosed.externalIhomMap`)

`F₁(E₁ ⟶ L₁) ⊗ F₂(E₂ ⟶ L₂) ⟶ (F₁ E₁ ⊗ F₂ E₂ ⟶ F₁ L₁ ⊗ F₂ L₂)`

is the transpose of the two evaluations, through the middle-four interchange `tensorμ`. For
external products of étale sheaves it is the map `β` of `lemma-external-duality-trace-morphism`
(iii).

This file proves the formal properties of this map used to show that `β` is an isomorphism:

* it is unchanged, up to the braidings, when the two factors are exchanged, for a symmetric `C`
  (`CategoryTheory.MonoidalClosed.externalIhomMap_swap`);
* for an adjunction `L ⊣ R` with an invertible projection formula
  `π : L M ⊗ N ≅ L (M ⊗ F N)` (a compactly supported direct image `g_!` and the exceptional
  inverse image `g^!`), the comparison `R (X ⟶ Y) ⟶ (F X ⟶ R Y)`
  (`CategoryTheory.Adjunction.projectionIhomMap`) is an isomorphism
  (`CategoryTheory.Adjunction.isIso_projectionIhomMap`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

/-- In a symmetric monoidal category, the middle-four interchange commutes with the braidings:
`tensorμ X₁ X₂ Y₁ Y₂ ≫ β = (β ⊗ β) ≫ tensorμ X₂ X₁ Y₂ Y₁`. -/
@[reassoc]
theorem SymmetricCategory.tensorμ_braiding {C : Type*} [Category* C] [MonoidalCategory C]
    [SymmetricCategory C] (X₁ X₂ Y₁ Y₂ : C) :
    tensorμ X₁ X₂ Y₁ Y₂ ≫ (β_ (X₁ ⊗ Y₁) (X₂ ⊗ Y₂)).hom =
      ((β_ X₁ X₂).hom ⊗ₘ (β_ Y₁ Y₂).hom) ≫ tensorμ X₂ X₁ Y₂ Y₁ := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y₂ X₁,
    SymmetricCategory.braiding_swap_eq_inv_braiding Y₁ X₂, tensorHom_def]

/-- In a symmetric monoidal category, braiding the two blocks and interchanging the middle
factors is interchanging the middle factors and braiding the two pairs:
`β ≫ tensorμ Y₁ Y₂ X₁ X₂ = tensorμ X₁ X₂ Y₁ Y₂ ≫ (β ⊗ β)`. -/
@[reassoc]
theorem SymmetricCategory.braiding_tensorμ {C : Type*} [Category* C] [MonoidalCategory C]
    [SymmetricCategory C] (X₁ X₂ Y₁ Y₂ : C) :
    (β_ (X₁ ⊗ X₂) (Y₁ ⊗ Y₂)).hom ≫ tensorμ Y₁ Y₂ X₁ X₂ =
      tensorμ X₁ X₂ Y₁ Y₂ ≫ ((β_ X₁ Y₁).hom ⊗ₘ (β_ X₂ Y₂).hom) := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding Y₂ X₁,
    SymmetricCategory.braiding_swap_eq_inv_braiding Y₁ X₂, tensorHom_def]

namespace MonoidalClosed

section External

universe v₀ v₁ v₂ u₀ u₁ u₂

variable {C : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} [Category.{v₀} C] [Category.{v₁} D₁]
  [Category.{v₂} D₂] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [MonoidalCategory D₁] [MonoidalClosed D₁] [MonoidalCategory D₂] [MonoidalClosed D₂]
  (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.LaxMonoidal] [F₂.LaxMonoidal]

/-- The external internal-hom map
`F₁(E₁ ⟶[D₁] L₁) ⊗ F₂(E₂ ⟶[D₂] L₂) ⟶ (F₁ E₁ ⊗ F₂ E₂ ⟶[C] F₁ L₁ ⊗ F₂ L₂)`: the transpose of
`(F₁ E₁ ⊗ F₂ E₂) ⊗ (F₁ H₁ ⊗ F₂ H₂) ⟶ (F₁ E₁ ⊗ F₁ H₁) ⊗ (F₂ E₂ ⊗ F₂ H₂) ⟶ F₁ L₁ ⊗ F₂ L₂`, the
middle-four interchange `tensorμ` followed by the images of the two evaluations
(`Hᵢ = Eᵢ ⟶ Lᵢ`). -/
noncomputable def externalIhomMap (E₁ L₁ : D₁) (E₂ L₂ : D₂) :
    F₁.obj ((ihom E₁).obj L₁) ⊗ F₂.obj ((ihom E₂).obj L₂) ⟶
      (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).obj (F₁.obj L₁ ⊗ F₂.obj L₂) :=
  curry (tensorμ _ _ _ _ ≫
    ((Functor.LaxMonoidal.μ F₁ _ _ ≫ F₁.map ((ihom.ev E₁).app L₁)) ⊗ₘ
      (Functor.LaxMonoidal.μ F₂ _ _ ≫ F₂.map ((ihom.ev E₂).app L₂))))

lemma uncurry_externalIhomMap (E₁ L₁ : D₁) (E₂ L₂ : D₂) :
    uncurry (externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂) = tensorμ _ _ _ _ ≫
      ((μ F₁ _ _ ≫ F₁.map ((ihom.ev E₁).app L₁)) ⊗ₘ (μ F₂ _ _ ≫ F₂.map ((ihom.ev E₂).app L₂))) :=
  uncurry_curry _

end External

section Swap

variable {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [MonoidalCategory D₁] [MonoidalClosed D₁]
  [MonoidalCategory D₂] [MonoidalClosed D₂] (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.LaxMonoidal]
  [F₂.LaxMonoidal]

/-- **Exchanging the two factors.** For a symmetric `C`, the external internal-hom map of
`(F₂, F₁)` is that of `(F₁, F₂)` conjugated by the braidings. -/
theorem externalIhomMap_swap (E₁ L₁ : D₁) (E₂ L₂ : D₂) :
    externalIhomMap F₂ F₁ E₂ L₂ E₁ L₁ = (β_ _ _).hom ≫ externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂ ≫
      (pre (β_ (F₂.obj E₂) (F₁.obj E₁)).hom).app _ ≫
        (ihom _).map (β_ (F₁.obj L₁) (F₂.obj L₂)).hom := by
  apply uncurry_injective
  rw [uncurry_natural_left, ← Category.assoc, uncurry_natural_right, uncurry_pre_app,
    uncurry_externalIhomMap, uncurry_externalIhomMap, Category.assoc, Category.assoc,
    whisker_exchange_assoc, ← tensorHom_def_assoc]
  erw [BraidedCategory.braiding_naturality]
  rw [SymmetricCategory.tensorμ_braiding_assoc, tensorHom_comp_tensorHom_assoc,
    SymmetricCategory.symmetry, SymmetricCategory.symmetry, id_tensorHom_id, Category.id_comp]

/-- The external internal-hom map of `(F₂, F₁)` is an isomorphism if and only if that of
`(F₁, F₂)` is. -/
theorem isIso_externalIhomMap_swap_iff (E₁ L₁ : D₁) (E₂ L₂ : D₂) :
    IsIso (externalIhomMap F₂ F₁ E₂ L₂ E₁ L₁) ↔ IsIso (externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂) := by
  have : IsIso ((pre (β_ (F₂.obj E₂) (F₁.obj E₁)).hom).app (F₁.obj L₁ ⊗ F₂.obj L₂)) :=
    isIso_pre_app _ _
  rw [externalIhomMap_swap, isIso_comp_left_iff, isIso_comp_right_iff]

end Swap

section BaseCase

/-- The transpose of `(ihomObjIsoTensor D X L).inv : D ⊗ L ⟶ (X ⟶ L)` is the transposed
evaluation `X ⊗ (D ⊗ L) ≅ (X ⊗ D) ⊗ L ⟶ L`. -/
lemma uncurry_ihomObjIsoTensor_inv {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] (D X L : C) [ExactPairing D X] :
    uncurry (ihomObjIsoTensor D X L).inv = (α_ _ _ _).inv ≫ ε_ D X ▷ L ≫ (λ_ L).hom := by
  have h₁ := (tensorLeftAdjunction D X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) L
  rw [tensorLeftAdjunction_counit_app] at h₁
  rw [uncurry_eq, ihomObjIsoTensor, ihomIsoTensorLeft, Iso.app_inv,
    Adjunction.rightAdjointUniq_inv_app, ← h₁]
  rfl

/-- **A criterion for maps into an internal hom out of an object with a left dual.** If `D` is
a left dual of `X`, a map `f : H ⟶ (X ⟶ L)` whose transpose is
`X ⊗ H ⟶ X ⊗ (D ⊗ L) ≅ (X ⊗ D) ⊗ L ⟶ L` for an isomorphism `g : H ⟶ D ⊗ L` is an isomorphism. -/
theorem isIso_of_uncurry_eq {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
    {D X L H : C} [ExactPairing D X] (g : H ⟶ D ⊗ L) [IsIso g] (f : H ⟶ (ihom X).obj L)
    (h : uncurry f = X ◁ g ≫ (α_ _ _ _).inv ≫ ε_ D X ▷ L ≫ (λ_ L).hom) : IsIso f := by
  have hf : f = g ≫ (ihomObjIsoTensor D X L).inv := by
    apply uncurry_injective
    rw [h, uncurry_natural_left, uncurry_ihomObjIsoTensor_inv]
  rw [hf]
  infer_instance

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : D ⥤ C) [F.Monoidal]

/-- For a monoidal functor `F` and a left dual `D'` of `E`, the image of the transposed evaluation
`E ⊗ (D' ⊗ L) ≅ (E ⊗ D') ⊗ L ⟶ L` is the transposed evaluation of the image pairing
(`CategoryTheory.ExactPairing.map`). -/
lemma _root_.CategoryTheory.Functor.whiskerLeft_μ_comp_μ_comp_map_evaluation (D' E L : D)
    [ExactPairing D' E] :
    F.obj E ◁ μ F D' L ≫ μ F E (D' ⊗ L) ≫
        F.map ((α_ E D' L).inv ≫ ε_ D' E ▷ L ≫ (λ_ L).hom) =
      (α_ _ _ _).inv ≫ (μ F E D' ≫ F.map (ε_ D' E) ≫ η F) ▷ F.obj L ≫ (λ_ _).hom := by
  rw [F.map_comp, F.map_comp, Functor.LaxMonoidal.associativity_inv_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.map_leftUnitor,
    Functor.Monoidal.μ_δ_assoc, comp_whiskerRight, comp_whiskerRight, Category.assoc,
    Category.assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]

variable [MonoidalClosed C]

/-- **Monoidal functors preserve internal homs out of objects with a left dual.** For a left
dual `D'` of `E` and a monoidal functor `F`, the transpose
`F (D' ⊗ L) ⟶ (F E ⟶ F L)` of the image of the transposed evaluation is an isomorphism. -/
theorem isIso_curry_μ_comp_map_evaluation (D' E L : D) [ExactPairing D' E] :
    IsIso (curry (μ F E (D' ⊗ L) ≫ F.map ((α_ E D' L).inv ≫ ε_ D' E ▷ L ≫ (λ_ L).hom))) := by
  let := ExactPairing.map F D' E
  refine isIso_of_uncurry_eq (δ F D' L) _ ?_
  rw [uncurry_curry, ← cancel_epi (F.obj E ◁ μ F D' L), ← whiskerLeft_comp_assoc,
    Functor.Monoidal.μ_δ, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  exact F.whiskerLeft_μ_comp_μ_comp_map_evaluation D' E L

/-- The exact pairing of `(X₁, X₂)` and `(Y₁, Y₂)` in a product of monoidal categories induced
by exact pairings of `X₁, Y₁` and of `X₂, Y₂`. -/
@[instance_reducible]
def _root_.CategoryTheory.ExactPairing.prod {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂] (X₁ Y₁ : C₁) (X₂ Y₂ : C₂) [ExactPairing X₁ Y₁]
    [ExactPairing X₂ Y₂] : ExactPairing ((X₁, X₂) : C₁ × C₂) (Y₁, Y₂) where
  coevaluation' := (η_ X₁ Y₁, η_ X₂ Y₂)
  evaluation' := (ε_ X₁ Y₁, ε_ X₂ Y₂)
  coevaluation_evaluation' := Prod.ext (ExactPairing.coevaluation_evaluation X₁ Y₁)
    (ExactPairing.coevaluation_evaluation X₂ Y₂)
  evaluation_coevaluation' := Prod.ext (ExactPairing.evaluation_coevaluation X₁ Y₁)
    (ExactPairing.evaluation_coevaluation X₂ Y₂)

variable [BraidedCategory C]

/-- **The external internal hom of two objects with left duals.** If `P₁, P₂` are left duals of
`A₁, A₂` in a braided monoidal closed category, the transpose of
`(A₁ ⊗ A₂) ⊗ ((P₁ ⊗ Q₁) ⊗ (P₂ ⊗ Q₂)) ⟶ (A₁ ⊗ (P₁ ⊗ Q₁)) ⊗ (A₂ ⊗ (P₂ ⊗ Q₂)) ⟶ Q₁ ⊗ Q₂`, the
middle-four interchange followed by the two transposed evaluations, is an isomorphism: it is the
case of the tensor product functor `C × C ⥤ C` in `isIso_curry_μ_comp_map_evaluation`. -/
theorem isIso_curry_tensorμ_comp_evaluation (P₁ A₁ Q₁ P₂ A₂ Q₂ : C) [ExactPairing P₁ A₁]
    [ExactPairing P₂ A₂] :
    IsIso (curry (tensorμ A₁ A₂ (P₁ ⊗ Q₁) (P₂ ⊗ Q₂) ≫
      (((α_ A₁ P₁ Q₁).inv ≫ ε_ P₁ A₁ ▷ Q₁ ≫ (λ_ Q₁).hom) ⊗ₘ
        ((α_ A₂ P₂ Q₂).inv ≫ ε_ P₂ A₂ ▷ Q₂ ≫ (λ_ Q₂).hom)))) := by
  let := ExactPairing.prod P₁ A₁ P₂ A₂
  exact isIso_curry_μ_comp_map_evaluation (tensor C) (P₁, P₂) (A₁, A₂) (Q₁, Q₂)

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] [MonoidalCategory D₁] [MonoidalClosed D₁]
  [MonoidalCategory D₂] [MonoidalClosed D₂] (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.Monoidal]
  [F₂.Monoidal]

/-- **The external internal-hom map of objects with left duals is an isomorphism.** If `E₁` and
`E₂` have left duals, then for monoidal functors `F₁`, `F₂` into a braided monoidal closed
category the external internal-hom map `F₁(E₁ ⟶ L₁) ⊗ F₂(E₂ ⟶ L₂) ⟶ (F₁ E₁ ⊗ F₂ E₂ ⟶ F₁ L₁ ⊗ F₂ L₂)`
is an isomorphism. -/
theorem isIso_externalIhomMap_of_exactPairing (D₁' E₁ L₁ : D₁) (D₂' E₂ L₂ : D₂)
    [ExactPairing D₁' E₁] [ExactPairing D₂' E₂] :
    IsIso (externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂) := by
  let := ExactPairing.map F₁ D₁' E₁
  let := ExactPairing.map F₂ D₂' E₂
  have h := isIso_curry_tensorμ_comp_evaluation (F₁.obj D₁') (F₁.obj E₁) (F₁.obj L₁)
    (F₂.obj D₂') (F₂.obj E₂) (F₂.obj L₂)
  let u₁ := μ F₁ D₁' L₁ ≫ F₁.map (ihomObjIsoTensor D₁' E₁ L₁).inv
  let u₂ := μ F₂ D₂' L₂ ≫ F₂.map (ihomObjIsoTensor D₂' E₂ L₂).inv
  have hu : (u₁ ⊗ₘ u₂) ≫ externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂ =
      curry (tensorμ _ _ _ _ ≫
        (((α_ _ _ _).inv ≫ ε_ (F₁.obj D₁') (F₁.obj E₁) ▷ _ ≫ (λ_ _).hom) ⊗ₘ
          ((α_ _ _ _).inv ≫ ε_ (F₂.obj D₂') (F₂.obj E₂) ▷ _ ≫ (λ_ _).hom))) := by
    rw [eq_curry_iff, uncurry_natural_left, uncurry_externalIhomMap, tensorμ_natural_right_assoc,
      tensorHom_comp_tensorHom]
    congr 2
    · rw [MonoidalCategory.whiskerLeft_comp_assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
        ← F₁.map_comp, ← uncurry_eq, uncurry_ihomObjIsoTensor_inv,
        F₁.whiskerLeft_μ_comp_μ_comp_map_evaluation]
      rfl
    · rw [MonoidalCategory.whiskerLeft_comp_assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
        ← F₂.map_comp, ← uncurry_eq, uncurry_ihomObjIsoTensor_inv,
        F₂.whiskerLeft_μ_comp_μ_comp_map_evaluation]
      rfl
  have : IsIso (u₁ ⊗ₘ u₂) := by unfold u₁ u₂; infer_instance
  rw [← hu] at h
  exact IsIso.of_isIso_comp_left (u₁ ⊗ₘ u₂) _

end BaseCase

end MonoidalClosed

namespace Adjunction

open MonoidalClosed

section ProjectionIhom

variable {C C' : Type*} [Category* C] [Category* C'] [MonoidalCategory C] [MonoidalCategory C']
  [SymmetricCategory C] [SymmetricCategory C'] [MonoidalClosed C] [MonoidalClosed C']
  {F : C ⥤ C'} {L : C' ⥤ C} {R : C ⥤ C'} (adj : L ⊣ R)
  (π : ∀ (M : C') (N : C), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]

/-- The comparison `R (X ⟶ Y) ⟶ (F X ⟶ R Y)` of an adjunction `L ⊣ R` with an invertible
projection map `π : L M ⊗ N ⟶ L (M ⊗ F N)`: the transpose of
`F X ⊗ R (X ⟶ Y) ≅ R (X ⟶ Y) ⊗ F X ⟶ R ((X ⟶ Y) ⊗ X) ≅ R (X ⊗ (X ⟶ Y)) ⟶ R Y`, the tensor map
(`CategoryTheory.Adjunction.projectionTensorMap`) followed by the evaluation. For the
exceptional inverse image `g^! = R` it is `g^! RHom(X, Y) ⟶ RHom(g^* X, g^! Y)`. -/
noncomputable def projectionIhomMap (X Y : C) :
    R.obj ((ihom X).obj Y) ⟶ (ihom (F.obj X)).obj (R.obj Y) :=
  curry ((β_ _ _).hom ≫ adj.projectionTensorMap π _ X ≫ R.map ((β_ _ X).hom ≫ (ihom.ev X).app Y))

/-- The transpose of `projectionIhomMap` on the right: the tensor map followed by the
evaluation. -/
lemma braiding_comp_uncurry_projectionIhomMap (X Y : C) :
    (β_ _ _).hom ≫ uncurry (adj.projectionIhomMap π X Y) =
      adj.projectionTensorMap π _ X ≫ R.map ((β_ _ X).hom ≫ (ihom.ev X).app Y) := by
  rw [projectionIhomMap, uncurry_curry, SymmetricCategory.symmetry_assoc]

variable (hπ : ∀ {M M' : C'} (φ : M ⟶ M') (N : C),
  L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
include hπ

/-- The image under `R` of a map into an internal hom, followed by `projectionIhomMap`, is the
transpose of the tensor map followed by the image of the uncurried map. -/
lemma map_comp_projectionIhomMap {H X Y : C} (f : H ⟶ (ihom X).obj Y) :
    R.map f ≫ adj.projectionIhomMap π X Y =
      curry ((β_ _ _).hom ≫ adj.projectionTensorMap π H X ≫
        R.map ((β_ H X).hom ≫ uncurry f)) := by
  rw [projectionIhomMap, ← curry_natural_left, BraidedCategory.braiding_naturality_right_assoc,
    projectionTensorMap_naturality_left_assoc adj π hπ, ← R.map_comp,
    BraidedCategory.braiding_naturality_left_assoc, ← uncurry_eq]

/-- **`R (X ⟶ Y) ≅ (F X ⟶ R Y)`.** The comparison `projectionIhomMap` is an isomorphism: by the
Yoneda lemma, maps `T ⟶ R (X ⟶ Y)` correspond to maps `L T ⊗ X ⟶ Y`, hence through the
projection formula to maps `L (T ⊗ F X) ⟶ Y`, i.e. to maps `T ⟶ (F X ⟶ R Y)`. -/
theorem isIso_projectionIhomMap (X Y : C) : IsIso (adj.projectionIhomMap π X Y) := by
  refine isIso_of_yoneda_map_bijective _ (fun T ↦ ?_)
  let e : (T ⟶ R.obj ((ihom X).obj Y)) ≃ (T ⟶ (ihom (F.obj X)).obj (R.obj Y)) :=
    (adj.homEquiv _ _).symm.trans <| ((ihom.adjunction X).homEquiv _ _).symm.trans <|
      (β_ (L.obj T) X).symm.homFromEquiv.trans <| (asIso (π T X)).homFromEquiv.trans <|
        (adj.homEquiv _ _).trans <| (β_ (F.obj X) T).symm.homFromEquiv.trans <|
          (ihom.adjunction (F.obj X)).homEquiv _ _
  have he : (fun t : T ⟶ R.obj ((ihom X).obj Y) ↦ t ≫ adj.projectionIhomMap π X Y) = e := by
    ext t
    simp only [e, Equiv.trans_apply, Iso.homFromEquiv_apply, asIso_inv, Iso.symm_inv,
      MonoidalClosed.homEquiv_symm_apply_eq]
    rw [projectionIhomMap, ← curry_natural_left, BraidedCategory.braiding_naturality_right_assoc]
    congr 2
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, homEquiv_counit, L.map_comp, L.map_comp, Category.assoc,
      Category.assoc, counit_naturality, map_projectionTensorMap_comp_counit_assoc,
      ← cancel_epi (π T X), IsIso.hom_inv_id_assoc, ← reassoc_of% (hπ t X),
      IsIso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left_assoc, ← uncurry_eq, homEquiv_counit]
    rfl
  rw [he]
  exact e.bijective

end ProjectionIhom

section TensorMap

variable {C C' : Type*} [Category* C] [Category* C'] [MonoidalCategory C] [MonoidalCategory C']
  [BraidedCategory C] [BraidedCategory C'] {F : C ⥤ C'} [F.Braided]

/-- For a braided monoidal functor `F`, the braiding of the first two of three factors commutes
with the tensor comparisons of `F`. -/
lemma _root_.CategoryTheory.Functor.whiskerLeft_μ_comp_μ_comp_map_braiding (a b c : C) :
    F.obj a ◁ μ F b c ≫ μ F a (b ⊗ c) ≫
        F.map ((α_ a b c).inv ≫ (β_ a b).hom ▷ c ≫ (α_ b a c).hom) =
      (α_ _ _ _).inv ≫ (β_ (F.obj a) (F.obj b)).hom ▷ F.obj c ≫ (α_ _ _ _).hom ≫
        F.obj b ◁ μ F a c ≫ μ F b (a ⊗ c) := by
  rw [F.map_comp, F.map_comp, Functor.LaxMonoidal.associativity_inv_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, ← comp_whiskerRight_assoc,
    Functor.LaxBraided.braided, comp_whiskerRight_assoc, Functor.LaxMonoidal.associativity]

variable {L : C' ⥤ C} {R : C ⥤ C'} (adj : L ⊣ R)
  (π : ∀ (M : C') (N : C), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]
  (hπ : ∀ {M M' : C'} (φ : M ⟶ M') (N : C),
    L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
  (hπr : ∀ (M : C') {N N' : C} (φ : N ⟶ N'),
    L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ F.map φ))
  (hassoc : ∀ (M : C') (N N' : C), π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
    L.map (α_ M (F.obj N) (F.obj N')).hom =
      (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ Functor.OplaxMonoidal.δ F N N'))
include hπ hπr hassoc

/-- **The tensor map commutes with the middle-four interchange.** For the tensor map
`τ M N : R M ⊗ F N ⟶ R (M ⊗ N)` of an adjunction with an associative projection formula and a
braided monoidal `F`,
`(τ M₁ M₂ ⊗ μ) ≫ τ (M₁ ⊗ M₂) (N₁ ⊗ N₂) ≫ R (tensorμ) = tensorμ ≫ (τ M₁ N₁ ⊗ μ) ≫ τ _ _`. -/
@[reassoc]
theorem projectionTensorMap_tensorμ (M₁ M₂ N₁ N₂ : C) :
    (adj.projectionTensorMap π M₁ M₂ ⊗ₘ μ F N₁ N₂) ≫
        adj.projectionTensorMap π (M₁ ⊗ M₂) (N₁ ⊗ N₂) ≫ R.map (tensorμ M₁ M₂ N₁ N₂) =
      tensorμ (R.obj M₁) (F.obj M₂) (F.obj N₁) (F.obj N₂) ≫
        (adj.projectionTensorMap π M₁ N₁ ⊗ₘ μ F M₂ N₂) ≫
          adj.projectionTensorMap π (M₁ ⊗ N₁) (M₂ ⊗ N₂) := by
  have hA (M : C) (N N' : C) : adj.projectionTensorMap π M N ▷ F.obj N' ≫
      adj.projectionTensorMap π (M ⊗ N) N' =
        (α_ _ _ _).hom ≫ R.obj M ◁ μ F N N' ≫ adj.projectionTensorMap π M (N ⊗ N') ≫
          R.map (α_ M N N').inv := by
    have h := projectionTensorMap_assoc adj π hπ (Functor.OplaxMonoidal.δ F) hassoc M N N'
    rw [Functor.Monoidal.inv_δ] at h
    rw [← cancel_mono (R.map (α_ M N N').hom), Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, ← R.map_comp, Iso.inv_hom_id, R.map_id, Category.comp_id, h]
  have hμ : tensorμ M₁ M₂ N₁ N₂ = (α_ _ _ _).hom ≫
      M₁ ◁ ((α_ M₂ N₁ N₂).inv ≫ (β_ M₂ N₁).hom ▷ N₂ ≫ (α_ N₁ M₂ N₂).hom) ≫ (α_ _ _ _).inv := by
    simp only [tensorμ, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  have hμ' : tensorμ (R.obj M₁) (F.obj M₂) (F.obj N₁) (F.obj N₂) = (α_ _ _ _).hom ≫
      R.obj M₁ ◁ ((α_ _ _ _).inv ≫ (β_ (F.obj M₂) (F.obj N₁)).hom ▷ F.obj N₂ ≫
        (α_ _ _ _).hom) ≫ (α_ _ _ _).inv := by
    simp only [tensorμ, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [tensorHom_def', tensorHom_def']
  simp only [Category.assoc]
  rw [reassoc_of% (hA M₁ M₂ (N₁ ⊗ N₂)), hA M₁ N₁ (M₂ ⊗ N₂), hμ, hμ']
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (α_ M₁ M₂ (N₁ ⊗ N₂)).inv, Iso.inv_hom_id, R.map_id, Category.id_comp,
    ← projectionTensorMap_naturality_right_assoc adj π hπr,
    ← associator_inv_naturality_right_assoc, Iso.inv_hom_id_assoc,
    associator_naturality_right_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc,
    Functor.whiskerLeft_μ_comp_μ_comp_map_braiding]

end TensorMap

section MonoidalNatTrans

variable {C₂ C C' : Type*} [Category* C₂] [Category* C] [Category* C'] [MonoidalCategory C₂]
  [MonoidalCategory C] [MonoidalCategory C'] [BraidedCategory C] [BraidedCategory C']
  {G : C ⥤ C'} [G.LaxBraided] {F₂ : C₂ ⥤ C} {F₂' : C₂ ⥤ C'} [F₂.LaxMonoidal] [F₂'.LaxMonoidal]

/-- A monoidal natural transformation `F₂ ⋙ G ⟶ F₂'`, for a braided `G`, commutes with the
transposed evaluations `F₂ B ⊗ F₂ A ≅ F₂ A ⊗ F₂ B ⟶ F₂ (A ⊗ B) ⟶ F₂ Z`. -/
lemma _root_.CategoryTheory.Functor.μ_comp_map_braiding_comp_app (e₂ : F₂ ⋙ G ⟶ F₂')
    (he₂ : ∀ X Y : C₂, μ G (F₂.obj X) (F₂.obj Y) ≫ G.map (μ F₂ X Y) ≫ e₂.app (X ⊗ Y) =
      (e₂.app X ⊗ₘ e₂.app Y) ≫ μ F₂' X Y) {A B Z : C₂} (f : A ⊗ B ⟶ Z) :
    μ G (F₂.obj B) (F₂.obj A) ≫ G.map ((β_ _ _).hom ≫ μ F₂ A B ≫ F₂.map f) ≫ e₂.app Z =
      (e₂.app B ⊗ₘ e₂.app A) ≫ (β_ _ _).hom ≫ μ F₂' A B ≫ F₂'.map f := by
  simp only [G.map_comp, Category.assoc]
  rw [Functor.LaxBraided.braided_assoc, ← Functor.comp_map,
    e₂.naturality, reassoc_of% (he₂ A B), BraidedCategory.braiding_naturality_assoc]
  rfl

end MonoidalNatTrans

section Step

variable {C₁ C₁' C₂ C C' : Type*} [Category* C₁] [Category* C₁'] [Category* C₂] [Category* C]
  [Category* C'] [MonoidalCategory C₁] [MonoidalCategory C₁'] [MonoidalCategory C₂]
  [MonoidalCategory C] [MonoidalCategory C'] [SymmetricCategory C₁] [SymmetricCategory C₁']
  [SymmetricCategory C] [SymmetricCategory C'] [MonoidalClosed C₁] [MonoidalClosed C₁']
  [MonoidalClosed C₂] [MonoidalClosed C] [MonoidalClosed C']
  {F₁ : C₁ ⥤ C} {F₂ : C₂ ⥤ C} {F₁' : C₁' ⥤ C'} {F₂' : C₂ ⥤ C'} [F₁.Braided] [F₂.LaxMonoidal]
  [F₁'.Braided] [F₂'.LaxMonoidal] {G : C ⥤ C'} [G.Braided] {G₁ : C₁ ⥤ C₁'}
  {L : C' ⥤ C} {R : C ⥤ C'} (adj : L ⊣ R)
  (π : ∀ (M : C') (N : C), L.obj M ⊗ N ⟶ L.obj (M ⊗ G.obj N)) [∀ M N, IsIso (π M N)]
  {L₁ : C₁' ⥤ C₁} {R₁ : C₁ ⥤ C₁'} (adj₁ : L₁ ⊣ R₁)
  (π₁ : ∀ (M : C₁') (N : C₁), L₁.obj M ⊗ N ⟶ L₁.obj (M ⊗ G₁.obj N)) [∀ M N, IsIso (π₁ M N)]
  (hπ : ∀ {M M' : C'} (φ : M ⟶ M') (N : C),
    L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ G.obj N))
  (hπ₁ : ∀ {M M' : C₁'} (φ : M ⟶ M') (N : C₁),
    L₁.map φ ▷ N ≫ π₁ M' N = π₁ M N ≫ L₁.map (φ ▷ G₁.obj N))
  (Ex : L₁ ⋙ F₁ ⟶ F₁' ⋙ L) [IsIso Ex] (ξ : TwoSquare F₁' L₁ L F₁)
  (hExξ : ∀ M : C₁', Ex.app M ≫ ξ.app M = 𝟙 _)
  (κ : ∀ N : C₁, F₁'.obj (G₁.obj N) ⟶ G.obj (F₁.obj N)) [∀ N, IsIso (κ N)]

omit [MonoidalClosed C₁] [MonoidalClosed C₁'] [MonoidalClosed C₂] [MonoidalClosed C]
  [MonoidalClosed C'] [∀ M N, IsIso (π M N)] [∀ M N, IsIso (π₁ M N)] [IsIso Ex]
  [∀ N, IsIso (κ N)] [SymmetricCategory C₁] [SymmetricCategory C₁'] [SymmetricCategory C]
  [SymmetricCategory C'] [F₁.Braided] [F₁'.Braided] [G.Braided] in
/-- The compatibility of the base change map `Ex : L₁ ⋙ F₁ ⟶ F₁' ⋙ L` with the projection maps
`π₁` of `L₁` and `π` of `L`, through the comonoidal structures of `F₁`, `F₁'` and the comparison
maps `κ N : F₁' G₁ N ⟶ G F₁ N`. -/
def ProjectionExchange (δ₁' : ∀ M N : C₁', F₁'.obj (M ⊗ N) ⟶ F₁'.obj M ⊗ F₁'.obj N)
    (δ₁ : ∀ M N : C₁, F₁.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₁.obj N) : Prop :=
  ∀ (M : C₁') (N : C₁), F₁.map (π₁ M N) ≫ Ex.app (M ⊗ G₁.obj N) ≫
    L.map (δ₁' M (G₁.obj N)) ≫ L.map (F₁'.obj M ◁ κ N) =
      δ₁ (L₁.obj M) N ≫ Ex.app M ▷ F₁.obj N ≫ π (F₁'.obj M) (F₁.obj N)

variable (hEx : ProjectionExchange π π₁ Ex κ (Functor.OplaxMonoidal.δ F₁')
  (Functor.OplaxMonoidal.δ F₁))

omit [MonoidalClosed C] [MonoidalClosed C'] [G.Braided] in
include hπ hExξ hEx in
/-- **The first factor.** The tensor map of `R` at `(F₁ H₁, F₁ E₁)` followed by the transposed
evaluation is, through the base change map `F₁' R₁ ⟶ R F₁` (the mate of `ξ`) and the
comparison `projectionIhomMap` of `R₁`, the transposed evaluation of `F₁'`. -/
lemma projectionTensorMap_comp_map_comp_inv_mateEquiv
    [∀ N, IsIso ((mateEquiv adj₁ adj ξ).app N)] (E₁ L₁ : C₁) :
    adj.projectionTensorMap π (F₁.obj ((ihom E₁).obj L₁)) (F₁.obj E₁) ≫
        R.map ((β_ _ _).hom ≫ μ F₁ _ _ ≫ F₁.map ((ihom.ev E₁).app L₁)) ≫
          inv ((mateEquiv adj₁ adj ξ).app L₁) =
      ((inv ((mateEquiv adj₁ adj ξ).app ((ihom E₁).obj L₁)) ≫
          F₁'.map (adj₁.projectionIhomMap π₁ E₁ L₁)) ⊗ₘ inv (κ E₁)) ≫
        (β_ _ _).hom ≫ μ F₁' _ _ ≫ F₁'.map ((ihom.ev (G₁.obj E₁)).app (R₁.obj L₁)) := by
  have hδb : ∀ {N N' : C₁} (φ : N ⟶ N') (N'' : C₁), F₁.map (φ ▷ N'') ≫
      Functor.OplaxMonoidal.δ F₁ N' N'' =
        Functor.OplaxMonoidal.δ F₁ N N'' ≫ F₁.map φ ▷ F₁.obj N'' :=
    fun φ N'' ↦ (Functor.OplaxMonoidal.δ_natural_left F₁ φ N'').symm
  have key := projectionTensorMap_mateEquiv adj₁ adj π₁ π hπ (Functor.OplaxMonoidal.δ F₁')
    (Functor.OplaxMonoidal.δ F₁) hδb κ Ex ξ hExξ hEx ((ihom E₁).obj L₁) E₁
  set BC := (mateEquiv adj₁ adj ξ)
  set H₁ := (ihom E₁).obj L₁
  -- solve `key` for the tensor map of `R`
  have key' : adj.projectionTensorMap π (F₁.obj H₁) (F₁.obj E₁) =
      (inv (BC.app H₁) ⊗ₘ inv (κ E₁)) ≫ μ F₁' _ _ ≫ F₁'.map (adj₁.projectionTensorMap π₁ H₁ E₁) ≫
        BC.app (H₁ ⊗ E₁) ≫ R.map (Functor.OplaxMonoidal.δ F₁ H₁ E₁) := by
    rw [key, ← Category.assoc (μ F₁' _ _), Functor.Monoidal.μ_δ, Category.id_comp,
      tensorHom_def, Category.assoc, whisker_exchange_assoc, ← comp_whiskerRight_assoc,
      IsIso.inv_hom_id, id_whiskerRight, Category.id_comp]
    erw [← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have hb : (β_ (F₁.obj H₁) (F₁.obj E₁)).hom ≫ μ F₁ E₁ H₁ =
      μ F₁ H₁ E₁ ≫ F₁.map (β_ H₁ E₁).hom := (Functor.LaxBraided.braided H₁ E₁).symm
  have hκ := adj₁.braiding_comp_uncurry_projectionIhomMap π₁ E₁ L₁
  rw [uncurry_eq, ← BraidedCategory.braiding_naturality_left_assoc] at hκ
  rw [key', reassoc_of% hb, R.map_comp (μ F₁ H₁ E₁)]
  simp only [Category.assoc]
  rw [← R.map_comp_assoc (Functor.OplaxMonoidal.δ F₁ H₁ E₁), Functor.Monoidal.δ_μ, R.map_id,
    Category.id_comp, ← F₁.map_comp, ← Functor.comp_map F₁ R, ← BC.naturality_assoc]
  dsimp only [Functor.id_obj]
  rw [IsIso.hom_inv_id, Category.comp_id, Functor.comp_map, ← F₁'.map_comp, ← hκ,
    F₁'.map_comp, F₁'.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxBraided.braided_assoc, tensorHom_def, tensorHom_def, Category.assoc,
    whisker_exchange_assoc, ← comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rfl

omit [SymmetricCategory C₁] [SymmetricCategory C₁'] [SymmetricCategory C] [SymmetricCategory C']
  [MonoidalClosed C₁] [MonoidalClosed C₁'] [MonoidalClosed C₂] [MonoidalClosed C]
  [MonoidalClosed C']
  [F₁.Braided] [F₂.LaxMonoidal] [F₁'.Braided] [F₂'.LaxMonoidal] [G.Braided] in
include hπ in
/-- The tensor map is natural in both variables. -/
@[reassoc]
lemma projectionTensorMap_map_tensorHom
    (hπr : ∀ (M : C') {N N' : C} (φ : N ⟶ N'),
      L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ G.map φ))
    {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N') :
    adj.projectionTensorMap π M N ≫ R.map (f ⊗ₘ g) =
      (R.map f ⊗ₘ G.map g) ≫ adj.projectionTensorMap π M' N' := by
  rw [tensorHom_def, R.map_comp, ← projectionTensorMap_naturality_left_assoc adj π hπ,
    ← projectionTensorMap_naturality_right adj π hπr, tensorHom_def, Category.assoc]

include hπ hπ₁ hExξ in
/-- **The external internal-hom map under an exceptional inverse image.** Let `R = g^!` be right
adjoint to `L = g_!` with an associative invertible projection formula for `G = g^*`, and let
`g` be the base change of `g₁ : Z₁' ⟶ Z₁` along the first projection, with base change map
`F₁' R₁ ⟶ R F₁` (the mate of `ξ`, where `F₁ = p₁^*`, `F₁' = p₁'^*`, `R₁ = g₁^!`) and an
isomorphism `F₂ ⋙ G ≅ F₂'` of the second projections. If the base change map and the tensor
maps of `R` at `(F₁ M, F₂ N)` are isomorphisms, then `R` of the external internal-hom map of
`(E₁, L₁, E₂, L₂)` is an isomorphism if and only if the external internal-hom map of
`(G₁ E₁, R₁ L₁, E₂, L₂)` is. -/
theorem isIso_map_externalIhomMap_iff
    (δ₁' : ∀ M N : C₁', F₁'.obj (M ⊗ N) ⟶ F₁'.obj M ⊗ F₁'.obj N)
    (hδ₁' : ∀ M N, δ₁' M N = Functor.OplaxMonoidal.δ F₁' M N)
    (δ₁ : ∀ M N : C₁, F₁.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₁.obj N)
    (hδ₁ : ∀ M N, δ₁ M N = Functor.OplaxMonoidal.δ F₁ M N)
    (hEx : ProjectionExchange π π₁ Ex κ δ₁' δ₁)
    (hπr : ∀ (M : C') {N N' : C} (φ : N ⟶ N'),
      L.obj M ◁ φ ≫ π M N' = π M N ≫ L.map (M ◁ G.map φ))
    (δG : ∀ N N' : C, G.obj (N ⊗ N') ⟶ G.obj N ⊗ G.obj N')
    (hδG : ∀ N N', δG N N' = Functor.OplaxMonoidal.δ G N N')
    (hassoc : ∀ (M : C') (N N' : C), π M N ▷ N' ≫ π (M ⊗ G.obj N) N' ≫
      L.map (α_ M (G.obj N) (G.obj N')).hom =
        (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ δG N N'))
    [∀ N, IsIso ((mateEquiv adj₁ adj ξ).app N)]
    (e₂ : F₂ ⋙ G ≅ F₂')
    (he₂ : ∀ X Y : C₂, μ G (F₂.obj X) (F₂.obj Y) ≫ G.map (μ F₂ X Y) ≫ e₂.hom.app (X ⊗ Y) =
      (e₂.hom.app X ⊗ₘ e₂.hom.app Y) ≫ μ F₂' X Y)
    [∀ M N, IsIso (adj.projectionTensorMap π (F₁.obj M) (F₂.obj N))]
    (E₁ L₁ : C₁) (E₂ L₂ : C₂) :
    IsIso (R.map (externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂)) ↔
      IsIso (externalIhomMap F₁' F₂' (G₁.obj E₁) (R₁.obj L₁) E₂ L₂) := by
  obtain rfl : δ₁' = Functor.OplaxMonoidal.δ F₁' := funext fun M ↦ funext (hδ₁' M)
  obtain rfl : δ₁ = Functor.OplaxMonoidal.δ F₁ := funext fun M ↦ funext (hδ₁ M)
  obtain rfl : δG = Functor.OplaxMonoidal.δ G := funext fun N ↦ funext (hδG N)
  set BC := (mateEquiv adj₁ adj ξ)
  set H₁ := (ihom E₁).obj L₁
  set H₂ := (ihom E₂).obj L₂
  have : IsIso (adj₁.projectionIhomMap π₁ E₁ L₁) := adj₁.isIso_projectionIhomMap π₁ hπ₁ E₁ L₁
  have : IsIso (adj.projectionIhomMap π (F₁.obj E₁ ⊗ F₂.obj E₂) (F₁.obj L₁ ⊗ F₂.obj L₂)) :=
    adj.isIso_projectionIhomMap π hπ _ _
  rw [← isIso_comp_right_iff _ (adj.projectionIhomMap π _ _), map_comp_projectionIhomMap adj π hπ]
  let a := inv (adj.projectionTensorMap π (F₁.obj H₁) (F₂.obj H₂)) ≫
    ((inv (BC.app H₁) ≫ F₁'.map (adj₁.projectionIhomMap π₁ E₁ L₁)) ⊗ₘ e₂.hom.app H₂)
  let c := Functor.OplaxMonoidal.δ G (F₁.obj E₁) (F₂.obj E₂) ≫ (inv (κ E₁) ⊗ₘ e₂.hom.app E₂)
  let d := inv (adj.projectionTensorMap π (F₁.obj L₁) (F₂.obj L₂)) ≫
    (inv (BC.app L₁) ⊗ₘ e₂.hom.app L₂)
  have hmain : adj.projectionTensorMap π _ _ ≫
      R.map ((β_ _ _).hom ≫ uncurry (externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂)) ≫ d =
      (a ⊗ₘ c) ≫ (β_ _ _).hom ≫
        uncurry (externalIhomMap F₁' F₂' (G₁.obj E₁) (R₁.obj L₁) E₂ L₂) := by
    rw [← cancel_epi (adj.projectionTensorMap π (F₁.obj H₁) (F₂.obj H₂) ⊗ₘ
      μ G (F₁.obj E₁) (F₂.obj E₂))]
    rw [uncurry_externalIhomMap, uncurry_externalIhomMap,
      SymmetricCategory.braiding_tensorμ_assoc, SymmetricCategory.braiding_tensorμ_assoc,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      R.map_comp]
    simp only [Category.assoc]
    rw [projectionTensorMap_tensorμ_assoc adj π hπ hπr hassoc,
      projectionTensorMap_map_tensorHom_assoc adj π hπ hπr]
    dsimp only [Functor.id_obj]
    simp only [a, c, d, IsIso.hom_inv_id_assoc, Functor.Monoidal.μ_δ_assoc,
      tensorHom_comp_tensorHom]
    rw [tensorμ_natural_assoc]
    congr 1
    rw [tensorHom_comp_tensorHom]
    congr 1
    · exact projectionTensorMap_comp_map_comp_inv_mateEquiv adj π adj₁ π₁ hπ Ex ξ hExξ κ hEx
        E₁ L₁
    · exact Functor.μ_comp_map_braiding_comp_app e₂.hom he₂ _
  have hd : IsIso d := by unfold d; infer_instance
  have hc : IsIso c := by unfold c; infer_instance
  have ha : IsIso a := by unfold a; infer_instance
  have h : curry ((β_ _ _).hom ≫ adj.projectionTensorMap π _ _ ≫
      R.map ((β_ _ _).hom ≫ uncurry (externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂))) =
      a ≫ externalIhomMap F₁' F₂' (G₁.obj E₁) (R₁.obj L₁) E₂ L₂ ≫ (pre c).app _ ≫
        (ihom _).map (inv d) := by
    apply uncurry_injective
    rw [uncurry_curry, uncurry_natural_left, ← Category.assoc, ← Category.assoc,
      uncurry_natural_right, Category.assoc, uncurry_pre_app, ← cancel_mono d, Category.assoc,
      Category.assoc, hmain, Category.assoc, Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, BraidedCategory.braiding_naturality_assoc, SymmetricCategory.symmetry_assoc,
      whisker_exchange_assoc, ← tensorHom_def_assoc]
  have : IsIso ((pre c).app (F₁'.obj (R₁.obj L₁) ⊗ F₂'.obj L₂)) := isIso_pre_app _ _
  rw [h, isIso_comp_left_iff, isIso_comp_right_iff]

end Step

end Adjunction

end CategoryTheory
