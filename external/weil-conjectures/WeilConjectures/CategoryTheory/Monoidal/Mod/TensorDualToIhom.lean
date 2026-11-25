/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomComp

/-!
# The morphism `X ⊗_A M^∨ ⟶ Hom_A(M, X)`

Let `A` be a commutative monoid in a symmetric monoidal Grothendieck abelian category `C`. For
`A`-modules `M` and `X`, with `M^∨ = Hom_A(M, A)`, we construct the morphism of `A`-modules
`X ⊗_A M^∨ ⟶ Hom_A(M, X)`, `x ⊗ φ ↦ (m ↦ x φ(m))` (`CategoryTheory.Mod.tensorDualToIhom`),
characterised by its uncurried form `(x ⊗ φ) ⊗ m ↦ x φ(m)`
(`CategoryTheory.Mod.tensorπ_tensorDualToIhom_evaluation`). It is natural in `X`
(`CategoryTheory.Mod.tensorDualToIhomNatTrans`) and in `M`
(`CategoryTheory.Mod.tensorLeftMap_app_comp_tensorDualToIhom`).

It is an isomorphism for `M = A` (`CategoryTheory.Mod.isIso_tensorDualToIhom_regular`), and the
class of `M` for which it is an isomorphism for all `X` is closed under isomorphisms and finite
direct sums; in particular it is an isomorphism for `M` free of finite rank
(`CategoryTheory.Mod.isIso_tensorDualToIhom_of_iso_biproduct`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A]

section Structural

omit [IsCommMonObj A] in
/-- `x (a b) = a (x b)` for the right action of a monoid on a module. -/
@[reassoc]
lemma whiskerLeft_mul_rightAct' (P : Mod C A) :
    P.X ◁ μ[A] ≫ rightAct P =
      (α_ P.X A A).inv ≫ (β_ P.X A).hom ▷ A ≫ (α_ A P.X A).hom ≫ A ◁ rightAct P ≫
        act P.X := by
  simp only [rightAct, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc, mul_act]
  monoidal

omit [IsCommMonObj A] in
/-- The right action is natural. -/
@[reassoc]
lemma rightAct_naturality {P Q : Mod C A} (f : P ⟶ Q) :
    f.hom ▷ A ≫ rightAct Q = rightAct P ≫ f.hom := by
  simp only [rightAct, BraidedCategory.braiding_naturality_left_assoc, Category.assoc, act_hom]

omit [IsCommMonObj A] in
/-- If `e : Y ⊗ M ⟶ A` is `A`-linear in `M`, so is `(x ⊗ y) ⊗ m ↦ x e(y ⊗ m)`. -/
lemma isLinearRight_whiskerLeft_rightAct {Y : C} {M : Mod C A} (P : Mod C A)
    (e : Y ⊗ M.X ⟶ A) (he : Y ◁ act M.X ≫ e =
      (α_ Y A M.X).inv ≫ (β_ Y A).hom ▷ M.X ≫ (α_ A Y M.X).hom ≫ A ◁ e ≫ μ[A]) :
    IsLinearRight (X := P.X ⊗ Y) (D := M) (N := P)
      ((α_ P.X Y M.X).hom ≫ P.X ◁ e ≫ rightAct P) := by
  unfold IsLinearRight
  rw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, he]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [whiskerLeft_mul_rightAct', associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, associator_naturality_right_assoc,
    BraidedCategory.braiding_tensor_left_hom]
  simp only [rightAct, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- `(x ⊗ y) ⊗ z ↦ x e(y ⊗ z)` is `A`-linear in `x`. -/
lemma rightAct_linear {Y Z : C} (P : Mod C A) (e : Y ⊗ Z ⟶ A) :
    ((α_ A P.X Y).inv ≫ act P.X ▷ Y) ▷ Z ≫ (α_ P.X Y Z).hom ≫ P.X ◁ e ≫ rightAct P =
      (α_ A (P.X ⊗ Y) Z).hom ≫ A ◁ ((α_ P.X Y Z).hom ≫ P.X ◁ e ≫ rightAct P) ≫
        act P.X := by
  rw [comp_whiskerRight_assoc, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    act_whiskerRight_rightAct]
  monoidal

omit [SymmetricCategory C] [IsCommMonObj A] in
/-- `(x ⊗ d) ⊗ z ↦ x e(d ⊗ z)` with `x (a b) = (x a) b` gives `x e((a d) ⊗ z) = (x a) e(d ⊗ z)`
when `e` is `A`-linear in `d`. -/
lemma rightAct_balanced_aux {Z : C} [BraidedCategory C] (P D : Mod C A) (e : D.X ⊗ Z ⟶ A)
    (he : act D.X ▷ Z ≫ e = (α_ A D.X Z).hom ≫ A ◁ e ≫ μ[A])
    (hP : P.X ◁ μ[A] ≫ rightAct P = (α_ P.X A A).inv ≫ rightAct P ▷ A ≫ rightAct P) :
    (P.X ◁ act D.X) ▷ Z ≫ (α_ P.X D.X Z).hom ≫ P.X ◁ e ≫ rightAct P =
      ((α_ P.X A D.X).inv ≫ rightAct P ▷ D.X) ▷ Z ≫ (α_ P.X D.X Z).hom ≫ P.X ◁ e ≫
        rightAct P := by
  rw [associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, he,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc, hP,
    associator_inv_naturality_right_assoc, comp_whiskerRight_assoc (α_ P.X A D.X).inv,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  monoidal

/-- If `e : D ⊗ Z ⟶ A` is `A`-linear in `D`, then `(x ⊗ d) ⊗ z ↦ x e(d ⊗ z)` is `A`-balanced
in `x` and `d`. -/
lemma rightAct_balanced {Z : C} (P D : Mod C A) (e : D.X ⊗ Z ⟶ A)
    (he : act D.X ▷ Z ≫ e = (α_ A D.X Z).hom ≫ A ◁ e ≫ μ[A]) :
    (P.X ◁ act D.X) ▷ Z ≫ (α_ P.X D.X Z).hom ≫ P.X ◁ e ≫ rightAct P =
      ((α_ P.X A D.X).inv ≫ rightAct P ▷ D.X) ▷ Z ≫ (α_ P.X D.X Z).hom ≫ P.X ◁ e ≫
        rightAct P :=
  rightAct_balanced_aux P D e he (whiskerLeft_mul_rightAct P)

omit [IsCommMonObj A] in
/-- `(x ⊗ y) ⊗ z ↦ x e(y ⊗ z)` is natural in the module of `x`. -/
lemma rightAct_naturality' {Y Z : C} {P Q : Mod C A} (f : P ⟶ Q) (e : Y ⊗ Z ⟶ A) :
    (f.hom ▷ Y) ▷ Z ≫ (α_ Q.X Y Z).hom ≫ Q.X ◁ e ≫ rightAct Q =
      (α_ P.X Y Z).hom ≫ P.X ◁ e ≫ rightAct P ≫ f.hom := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightAct_naturality]

end Structural

variable [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

variable (M X : Mod C A)

/-- The morphism `(x ⊗ φ) ⊗ m ↦ x φ(m)`, `X ⊗ M^∨ ⊗ M ⟶ X`. -/
noncomputable def tensorDualToIhomAux :
    (X.X ⊗ ((ihom M).obj (regular A)).X) ⊗ M.X ⟶ X.X :=
  (α_ _ _ _).hom ≫ X.X ◁ evaluation M (regular A) ≫ rightAct X

lemma isLinearRight_tensorDualToIhomAux :
    IsLinearRight (D := M) (N := X) (tensorDualToIhomAux M X) :=
  isLinearRight_whiskerLeft_rightAct X (evaluation M (regular A))
    (isLinearRight_evaluation M (regular A))

/-- The morphism `X ⊗ M^∨ ⟶ Hom_A(M, X)`, `x ⊗ φ ↦ (m ↦ x φ(m))`, of underlying objects. -/
noncomputable def tensorDualToIhomCurry :
    X.X ⊗ ((ihom M).obj (regular A)).X ⟶ ((ihom M).obj X).X :=
  curry (tensorDualToIhomAux M X) (isLinearRight_tensorDualToIhomAux M X)

@[reassoc]
lemma tensorDualToIhomCurry_evaluation :
    tensorDualToIhomCurry M X ▷ M.X ≫ evaluation M X = tensorDualToIhomAux M X :=
  curry_evaluation _ _

lemma isBilinear_tensorDualToIhomCurry :
    IsBilinear (P := X) (M := (ihom M).obj (regular A)) (N := (ihom M).obj X)
      (tensorDualToIhomCurry M X) where
  linear := by
    apply hom_ext_of_evaluation
    have h := rightAct_linear X (evaluation M (regular A))
    simp only [comp_whiskerRight, Category.assoc] at h
    simp only [comp_whiskerRight, Category.assoc, tensorDualToIhomCurry_evaluation]
    rw [act_whiskerRight_evaluation, associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, tensorDualToIhomCurry_evaluation]
    exact h
  balanced := by
    apply hom_ext_of_evaluation
    have h := rightAct_balanced X _ (evaluation M (regular A))
      (act_whiskerRight_evaluation M (regular A))
    simp only [comp_whiskerRight, Category.assoc] at h
    simp only [comp_whiskerRight, Category.assoc, tensorDualToIhomCurry_evaluation]
    exact h

/-- **The morphism `X ⊗_A M^∨ ⟶ Hom_A(M, X)`**, `x ⊗ φ ↦ (m ↦ x φ(m))`. -/
noncomputable def tensorDualToIhom :
    (tensorLeft ((ihom M).obj (regular A))).obj X ⟶ (ihom M).obj X :=
  tensorDesc _ (isBilinear_tensorDualToIhomCurry M X)

@[reassoc]
lemma tensorπ_tensorDualToIhom :
    tensorπ X ((ihom M).obj (regular A)) ≫ (tensorDualToIhom M X).hom =
      tensorDualToIhomCurry M X :=
  tensorπ_tensorDesc _ _

/-- The uncurried form of `X ⊗_A M^∨ ⟶ Hom_A(M, X)` is `(x ⊗ φ) ⊗ m ↦ x φ(m)`. -/
lemma tensorπ_tensorDualToIhom_evaluation :
    (tensorπ X ((ihom M).obj (regular A)) ≫ (tensorDualToIhom M X).hom) ▷ M.X ≫
      evaluation M X = tensorDualToIhomAux M X := by
  rw [tensorπ_tensorDualToIhom, tensorDualToIhomCurry_evaluation]

variable {M X} in
/-- Morphisms `X ⊗_A D ⟶ Hom_A(M, N)` are determined by their uncurried forms
`(x ⊗ d) ⊗ m ↦ f(x ⊗ d)(m)`. -/
lemma tensorLeft_ihom_hom_ext {D N : Mod C A} {f g : (tensorLeft D).obj X ⟶ (ihom M).obj N}
    (h : (tensorπ X D ≫ f.hom) ▷ M.X ≫ evaluation M N =
      (tensorπ X D ≫ g.hom) ▷ M.X ≫ evaluation M N) : f = g :=
  tensorLeft_obj_hom_ext (hom_ext_of_evaluation h)

variable {X} in
/-- `X ⊗_A M^∨ ⟶ Hom_A(M, X)` is natural in `X`. -/
@[reassoc]
lemma tensorDualToIhom_naturality {X' : Mod C A} (f : X ⟶ X') :
    (tensorLeft ((ihom M).obj (regular A))).map f ≫ tensorDualToIhom M X' =
      tensorDualToIhom M X ≫ (ihom M).map f := by
  refine tensorLeft_ihom_hom_ext ?_
  rw [Mod.comp_hom', tensorπ_map_assoc, comp_whiskerRight_assoc,
    tensorπ_tensorDualToIhom_evaluation, Mod.comp_hom', ← Category.assoc,
    comp_whiskerRight_assoc, evaluation_naturality, ← Category.assoc,
    tensorπ_tensorDualToIhom_evaluation]
  rw [tensorDualToIhomAux, tensorDualToIhomAux, Category.assoc, Category.assoc]
  exact rightAct_naturality' f (evaluation M (regular A))

/-- `X ⊗_A M^∨ ⟶ Hom_A(M, X)`, as a natural transformation `- ⊗_A M^∨ ⟶ Hom_A(M, -)`. -/
@[simps]
noncomputable def tensorDualToIhomNatTrans :
    tensorLeft ((ihom M).obj (regular A)) ⟶ ihom M where
  app := tensorDualToIhom M
  naturality _ _ f := tensorDualToIhom_naturality M f

variable {M} in
/-- `X ⊗_A M^∨ ⟶ Hom_A(M, X)` is natural in `M`. -/
@[reassoc]
lemma tensorLeftMap_app_comp_tensorDualToIhom {M' : Mod C A} (f : M ⟶ M') :
    (tensorLeftMap ((ihomMap f).app (regular A))).app X ≫ tensorDualToIhom M X =
      tensorDualToIhom M' X ≫ (ihomMap f).app X := by
  refine tensorLeft_ihom_hom_ext ?_
  rw [Mod.comp_hom', tensorπ_tensorLeftMap_assoc, comp_whiskerRight_assoc,
    tensorπ_tensorDualToIhom_evaluation, Mod.comp_hom', ← Category.assoc,
    comp_whiskerRight_assoc, evaluation_ihomMap, ← whisker_exchange_assoc,
    tensorπ_tensorDualToIhom_evaluation, tensorDualToIhomAux, tensorDualToIhomAux,
    associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    evaluation_ihomMap, associator_naturality_right_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc]

omit [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)] in
/-- `x (b a) = (x b) a`. -/
lemma whiskerLeft_rightAct_regular_rightAct (P : Mod C A) :
    P.X ◁ rightAct (regular A) ≫ rightAct P =
      (α_ P.X A A).inv ≫ rightAct P ▷ A ≫ rightAct P := by
  have h : rightAct (regular A) = μ[A] := IsCommMonObj.mul_comm A
  rw [h]
  exact whiskerLeft_mul_rightAct P

omit [MonoidalPreadditive C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)] in
/-- The quotient map `P ⊗ A ⟶ P ⊗_A A ≅ P` is the right action. -/
@[reassoc]
lemma tensorπ_tensorLeftRegularHom_app (P : Mod C A) :
    tensorπ P (regular A) ≫ (tensorLeftRegularHom.app P).hom = rightAct P :=
  congrArg Mod.Hom.hom (tensorLeftπ_tensorLeftRegularHom_app P)

omit [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)] in
/-- The computation behind `CategoryTheory.Mod.tensorDualToIhom_regular`, stated for arbitrary
morphisms `ev = e ▷ A ≫ μ` and `ev' = i ▷ A ≫ ρ` with `j ≫ i = 𝟙`. -/
lemma tensorDualToIhom_regular_aux {F G : C} (P : Mod C A) (e : F ⟶ A) (ev : F ⊗ A ⟶ A)
    (hev : ev = e ▷ A ≫ μ[A]) (i : G ⟶ P.X) (j : P.X ⟶ G) (hji : j ≫ i = 𝟙 _)
    (ev' : G ⊗ A ⟶ P.X) (hev' : ev' = i ▷ A ≫ rightAct P) :
    (α_ P.X F A).hom ≫ P.X ◁ ev ≫ rightAct P =
      (P.X ◁ e ≫ (β_ P.X A).hom ≫ act P.X ≫ j) ▷ A ≫ ev' := by
  subst hev hev'
  rw [MonoidalCategory.whiskerLeft_comp_assoc, whiskerLeft_mul_rightAct,
    associator_inv_naturality_middle_assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc (P.X ◁ e ≫ (β_ P.X A).hom ≫ act P.X ≫ j) i, Category.assoc,
    Category.assoc, Category.assoc, hji, Category.comp_id]
  simp only [comp_whiskerRight, Category.assoc]

/-- For `M = A`, `X ⊗_A A^∨ ⟶ Hom_A(A, X)` is the composite of the isomorphisms
`X ⊗_A A^∨ ≅ X ⊗_A A ≅ X ≅ Hom_A(A, X)`. -/
lemma tensorDualToIhom_regular :
    tensorDualToIhom (regular A) X =
      (tensorLeftMap (ihomRegularIso.hom.app (regular A))).app X ≫
        tensorLeftRegularHom.app X ≫ ihomRegularIso.inv.app X := by
  refine tensorLeft_ihom_hom_ext ?_
  rw [tensorπ_tensorDualToIhom_evaluation, Mod.comp_hom', tensorπ_tensorLeftMap_assoc,
    Mod.comp_hom']
  erw [tensorπ_tensorLeftRegularHom_app_assoc]
  have h : rightAct (regular A) = μ[A] := IsCommMonObj.mul_comm A
  exact tensorDualToIhom_regular_aux X _ (evaluation (regular A) (regular A))
    ((evaluation_regular (regular A)).trans (by rw [h])) _ _
    (congrArg Mod.Hom.hom (ihomRegularIso.inv_hom_id_app X)) (evaluation (regular A) X)
    (evaluation_regular X)

instance isIso_tensorDualToIhom_regular : IsIso (tensorDualToIhom (regular A) X) := by
  rw [tensorDualToIhom_regular]
  have : IsIso ((tensorLeftMap (ihomRegularIso.hom.app (regular A))).app X) :=
    inferInstanceAs (IsIso ((tensorLeftMapIso (ihomRegularIso.app (regular A))).hom.app X))
  infer_instance

attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

/-- `M ↦ X ⊗_A M^∨` on morphisms, an additive contravariant functor. -/
noncomputable def tensorDualMap {M M' : Mod C A} (f : M ⟶ M') :
    (tensorLeft ((ihom M').obj (regular A))).obj X ⟶
      (tensorLeft ((ihom M).obj (regular A))).obj X :=
  (tensorLeftMap ((ihomMap f).app (regular A))).app X

variable {M} in
@[reassoc]
lemma tensorDualMap_comp_tensorDualToIhom {M' : Mod C A} (f : M ⟶ M') :
    tensorDualMap X f ≫ tensorDualToIhom M X = tensorDualToIhom M' X ≫ (ihomMap f).app X :=
  tensorLeftMap_app_comp_tensorDualToIhom X f

lemma tensorDualMap_comp {M M' M'' : Mod C A} (f : M ⟶ M') (g : M' ⟶ M'') :
    tensorDualMap X (f ≫ g) = tensorDualMap X g ≫ tensorDualMap X f := by
  rw [tensorDualMap, ihomMap_comp, NatTrans.comp_app, tensorLeftMap_comp]
  rfl

lemma tensorDualMap_id : tensorDualMap X (𝟙 M) = 𝟙 _ := by
  rw [tensorDualMap, ihomMap_id, NatTrans.id_app, tensorLeftMap_id]
  rfl

/-- `M ↦ X ⊗_A M^∨` is additive on morphisms. -/
noncomputable def tensorDualMapAddHom (M M' : Mod C A) :
    (M ⟶ M') →+ ((tensorLeft ((ihom M').obj (regular A))).obj X ⟶
      (tensorLeft ((ihom M).obj (regular A))).obj X) :=
  AddMonoidHom.mk' (tensorDualMap X) fun f g ↦ by
    rw [tensorDualMap, ihomMap_add, NatTrans.app_add, tensorLeftMap_add, NatTrans.app_add]
    rfl

/-- **`X ⊗_A M^∨ ⟶ Hom_A(M, X)` for finite direct sums**: if it is an isomorphism for each `Mᵢ`,
it is one for `⨁ᵢ Mᵢ`. -/
lemma isIso_tensorDualToIhom_biproduct {n : ℕ} (M : Fin n → Mod C A)
    (h : ∀ i, IsIso (tensorDualToIhom (M i) X)) : IsIso (tensorDualToIhom (⨁ M) X) := by
  refine ⟨∑ i, (ihomMap (biproduct.ι M i)).app X ≫ inv (tensorDualToIhom (M i) X) ≫
    tensorDualMap X (biproduct.π M i), ?_, ?_⟩
  · simp_rw [Preadditive.comp_sum, ← tensorDualMap_comp_tensorDualToIhom_assoc,
      IsIso.hom_inv_id_assoc, ← tensorDualMap_comp]
    calc _ = tensorDualMapAddHom X _ _ (∑ i, biproduct.π M i ≫ biproduct.ι M i) := by
          rw [map_sum]
          rfl
      _ = 𝟙 _ := by
          rw [biproduct.total]
          exact tensorDualMap_id _ X
  · simp_rw [Preadditive.sum_comp, Category.assoc, tensorDualMap_comp_tensorDualToIhom,
      IsIso.inv_hom_id_assoc, ← NatTrans.comp_app,
      ← NatTrans.app_sum, sum_ihomMap_ι_comp_ihomMap_π]
    rfl

/-- `X ⊗_A M^∨ ⟶ Hom_A(M, X)` is an isomorphism for `M` free of finite rank. -/
lemma isIso_tensorDualToIhom_of_iso_biproduct {M : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) : IsIso (tensorDualToIhom M X) := by
  have : IsIso (tensorDualToIhom (⨁ fun _ : Fin n ↦ regular A) X) :=
    isIso_tensorDualToIhom_biproduct X _ fun _ ↦ inferInstance
  have : IsIso (tensorDualMap X e.hom) :=
    inferInstanceAs (IsIso ((tensorLeftMapIso ((ihomMapIso e).app (regular A))).hom.app X))
  have : IsIso ((ihomMap e.hom).app X) := inferInstanceAs (IsIso ((ihomMapIso e).hom.app X))
  have := tensorDualMap_comp_tensorDualToIhom X e.hom
  have : IsIso (tensorDualMap X e.hom ≫ tensorDualToIhom M X) := by
    rw [this]
    infer_instance
  exact IsIso.of_isIso_comp_left (tensorDualMap X e.hom) _

end CategoryTheory.Mod
