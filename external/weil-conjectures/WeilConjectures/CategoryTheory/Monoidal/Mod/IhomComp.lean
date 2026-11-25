/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-!
# Internal composition of internal homs of modules

Let `A` be a commutative monoid in a symmetric monoidal Grothendieck abelian category `C`.

* A morphism `q : (P ⊗ M) ⊗ N ⟶ Q` of underlying objects which is `A`-linear in each variable
  is the twice uncurried form of a morphism of `A`-modules `P ⟶ Hom_A(M, Hom_A(N, Q))`
  (`CategoryTheory.Mod.curryHom₂`); such morphisms are determined by their twice uncurried form
  (`CategoryTheory.Mod.hom_ext₂`).
* The internal composition `Hom_A(N, K) ⟶ Hom_A(Hom_A(M, N), Hom_A(M, K))`, `g ↦ (f ↦ g ∘ f)`
  (`CategoryTheory.Mod.ihomComp`).
* The comparison `Hom_A(Hom_A(Hom_A(a, H), L), K) ⟶ Hom_A(a, Hom_A(Hom_A(H, L), K))`,
  `f ↦ (x ↦ (y ↦ f (t ↦ y (t x))))` (`CategoryTheory.Mod.ihomIhomComparison`). It is natural in
  `a` and `K`, and an isomorphism for `a = A` and hence for `a` free of finite rank
  (`CategoryTheory.Mod.isIso_ihomIhomComparison_free`). For `L = A` it identifies the tensor
  product with `a^∨` followed by the tensor product with `H^∨` with the tensor product with
  `Hom_A(a, H)^∨`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

section Curry

variable {X : C} {N Q : Mod C A} (q : X ⊗ N.X ⟶ Q.X) (hq : IsLinearRight q)

/-- A criterion for a morphism into the curried form `curry q` to factor through the action:
it suffices to check it after uncurrying. -/
lemma comp_curry_eq {Z : C} (f : Z ⟶ X) (g : Z ⟶ A ⊗ X)
    (h : f ▷ N.X ≫ q = g ▷ N.X ≫ (α_ A X N.X).hom ≫ A ◁ q ≫ act Q.X) :
    f ≫ curry q hq = g ≫ A ◁ curry q hq ≫ act ((ihom N).obj Q).X := by
  apply hom_ext_of_evaluation (D := N)
  rw [comp_whiskerRight_assoc, curry_evaluation, h, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, act_whiskerRight_evaluation, associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, curry_evaluation]

end Curry

/-- **Currying.** A morphism `q : M ⊗ D ⟶ N` of underlying objects which is `A`-linear in `D`
and in `M` is the uncurried form of a morphism of `A`-modules `M ⟶ Hom_A(D, N)`. -/
noncomputable def curryHomOfLinear {M D N : Mod C A} (q : M.X ⊗ D.X ⟶ N.X)
    (hq : IsLinearRight q)
    (hq' : act M.X ▷ D.X ≫ q = (α_ A M.X D.X).hom ≫ A ◁ q ≫ act N.X) :
    M ⟶ (ihom D).obj N :=
  homMk (curry q hq) (by
    apply hom_ext_of_evaluation (D := D)
    rw [comp_whiskerRight, Category.assoc, curry_evaluation, hq', comp_whiskerRight,
      Category.assoc, act_whiskerRight_evaluation, associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, curry_evaluation])

/-- The underlying morphism of `curryHomOfLinear q` is `curry q`. -/
lemma curryHomOfLinear_hom {M D N : Mod C A} (q : M.X ⊗ D.X ⟶ N.X) (hq : IsLinearRight q)
    (hq' : act M.X ▷ D.X ≫ q = (α_ A M.X D.X).hom ≫ A ◁ q ≫ act N.X) :
    (curryHomOfLinear q hq hq').hom = curry q hq :=
  rfl


@[simp]
lemma uncurryHom_curryHomOfLinear {M D N : Mod C A} (q : M.X ⊗ D.X ⟶ N.X)
    (hq : IsLinearRight q)
    (hq' : act M.X ▷ D.X ≫ q = (α_ A M.X D.X).hom ≫ A ◁ q ≫ act N.X) :
    uncurryHom (curryHomOfLinear q hq hq') = q :=
  curry_evaluation q hq

section Curry₂

variable {P M N Q : Mod C A} (q : (P.X ⊗ M.X) ⊗ N.X ⟶ Q.X) (h₁ : IsLinearRight q)
  (h₂ : (P.X ◁ act M.X) ▷ N.X ≫ q =
    ((α_ P.X A M.X).inv ≫ (β_ P.X A).hom ▷ M.X ≫ (α_ A P.X M.X).hom) ▷ N.X ≫
      (α_ A (P.X ⊗ M.X) N.X).hom ≫ A ◁ q ≫ act Q.X)
  (h₃ : (act P.X ▷ M.X) ▷ N.X ≫ q =
    (α_ A P.X M.X).hom ▷ N.X ≫ (α_ A (P.X ⊗ M.X) N.X).hom ≫ A ◁ q ≫ act Q.X)

/-- **Currying twice.** The morphism `P ⟶ Hom_A(M, Hom_A(N, Q))` whose twice uncurried form is a
morphism `q : (P ⊗ M) ⊗ N ⟶ Q` which is `A`-linear in each variable. -/
noncomputable def curryHom₂ (q : (P.X ⊗ M.X) ⊗ N.X ⟶ Q.X) (h₁ : IsLinearRight q)
    (h₂ : (P.X ◁ act M.X) ▷ N.X ≫ q =
      ((α_ P.X A M.X).inv ≫ (β_ P.X A).hom ▷ M.X ≫ (α_ A P.X M.X).hom) ▷ N.X ≫
        (α_ A (P.X ⊗ M.X) N.X).hom ≫ A ◁ q ≫ act Q.X)
    (h₃ : (act P.X ▷ M.X) ▷ N.X ≫ q =
      (α_ A P.X M.X).hom ▷ N.X ≫ (α_ A (P.X ⊗ M.X) N.X).hom ≫ A ◁ q ≫ act Q.X) :
    P ⟶ (ihom M).obj ((ihom N).obj Q) :=
  curryHomOfLinear (curry q h₁)
    ((comp_curry_eq q h₁ _ _ h₂).trans (by simp only [Category.assoc]))
    (comp_curry_eq q h₁ _ _ h₃)

/-- The twice uncurried form of `curryHom₂ q` is `q`. -/
lemma uncurryHom_curryHom₂ :
    uncurryHom (curryHom₂ q h₁ h₂ h₃) ▷ N.X ≫ evaluation N Q = q := by
  rw [curryHom₂, uncurryHom_curryHomOfLinear, curry_evaluation]

end Curry₂

/-- Morphisms into a twice iterated internal hom are determined by their twice uncurried
form. -/
lemma hom_ext₂ {P M N Q : Mod C A} {v w : P ⟶ (ihom M).obj ((ihom N).obj Q)}
    (h : uncurryHom v ▷ N.X ≫ evaluation N Q = uncurryHom w ▷ N.X ≫ evaluation N Q) :
    v = w :=
  uncurryHom_injective (hom_ext_of_evaluation h)

/-- The evaluation `Hom_A(M, N) ⊗ M ⟶ N` is `A`-linear in `M`. -/
lemma isLinearRight_evaluation (M N : Mod C A) :
    IsLinearRight (X := ((ihom M).obj N).X) (evaluation M N) := by
  rw [IsLinearRight, whiskerLeft_act_evaluation]
  simp only [rightAct, comp_whiskerRight, Category.assoc]
  rw [act_whiskerRight_evaluation]

section IhomComp

variable (M N K : Mod C A)

/-- The uncurried internal composition `(g ⊗ f) ⊗ m ↦ g (f m)`. -/
noncomputable abbrev ihomCompUncurried :
    (((ihom N).obj K).X ⊗ ((ihom M).obj N).X) ⊗ M.X ⟶ K.X :=
  (α_ _ _ _).hom ≫ ((ihom N).obj K).X ◁ evaluation M N ≫ evaluation N K

/-- The uncurried internal composition is `A`-linear in the third variable. -/
lemma isLinearRight_ihomCompUncurried : IsLinearRight (ihomCompUncurried M N K) := by
  have h₁ := isLinearRight_evaluation M N
  have h₂ := isLinearRight_evaluation N K
  rw [IsLinearRight] at h₁ h₂
  rw [IsLinearRight]
  unfold ihomCompUncurried
  rw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, h₁]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [h₂, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, BraidedCategory.braiding_tensor_left_hom]
  simp only [comp_whiskerRight, Category.assoc]
  monoidal

/-- The uncurried internal composition is `A`-linear in the second variable. -/
lemma ihomCompUncurried_linear_middle :
    (((ihom N).obj K).X ◁ act ((ihom M).obj N).X) ▷ M.X ≫ ihomCompUncurried M N K =
      ((α_ _ A _).inv ≫ (β_ ((ihom N).obj K).X A).hom ▷ _ ≫ (α_ A _ _).hom) ▷ M.X ≫
        (α_ A _ M.X).hom ≫ A ◁ ihomCompUncurried M N K ≫ act K.X := by
  have h₂ := isLinearRight_evaluation N K
  rw [IsLinearRight] at h₂
  unfold ihomCompUncurried
  rw [associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    act_whiskerRight_evaluation]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [h₂, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]
  monoidal

/-- The uncurried internal composition is `A`-linear in the first variable. -/
lemma ihomCompUncurried_linear_left :
    (act ((ihom N).obj K).X ▷ ((ihom M).obj N).X) ▷ M.X ≫ ihomCompUncurried M N K =
      (α_ A _ _).hom ▷ M.X ≫ (α_ A _ M.X).hom ≫ A ◁ ihomCompUncurried M N K ≫ act K.X := by
  unfold ihomCompUncurried
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, act_whiskerRight_evaluation]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- **Internal composition** `Hom_A(N, K) ⟶ Hom_A(Hom_A(M, N), Hom_A(M, K))`,
`g ↦ (f ↦ g ∘ f)`. -/
noncomputable def ihomComp :
    (ihom N).obj K ⟶ (ihom ((ihom M).obj N)).obj ((ihom M).obj K) :=
  curryHom₂ (ihomCompUncurried M N K) (isLinearRight_ihomCompUncurried M N K)
    (ihomCompUncurried_linear_middle M N K) (ihomCompUncurried_linear_left M N K)

/-- The twice uncurried form of the internal composition. -/
lemma uncurryHom_ihomComp :
    uncurryHom (ihomComp M N K) ▷ M.X ≫ evaluation M K = ihomCompUncurried M N K :=
  uncurryHom_curryHom₂ _ _ _ _

end IhomComp

/-- The uncurried form of the identity of `Hom_A(M, N)` is the evaluation. -/
lemma uncurryHom_id (M N : Mod C A) : uncurryHom (𝟙 ((ihom M).obj N)) = evaluation M N := by
  rw [uncurryHom, Mod.id_hom', id_whiskerRight, Category.id_comp]

section Compare

variable (a H L K : Mod C A)

/-- The morphism `a ⟶ Hom_A(Hom_A(H, L), Hom_A(Hom_A(a, H), L))`, `x ↦ (y ↦ (t ↦ y (t x)))`. -/
noncomputable def toIhomIhom :
    a ⟶ (ihom ((ihom H).obj L)).obj ((ihom ((ihom a).obj H)).obj L) :=
  transpose (𝟙 ((ihom a).obj H)) ≫ transpose (ihomComp ((ihom a).obj H) H L)

/-- The comparison `Hom_A(Hom_A(Hom_A(a, H), L), K) ⟶ Hom_A(a, Hom_A(Hom_A(H, L), K))`,
`f ↦ (x ↦ (y ↦ f (t ↦ y (t x))))`; it is an isomorphism for `a` locally free of finite rank. -/
noncomputable def ihomIhomComparison :
    (ihom ((ihom ((ihom a).obj H)).obj L)).obj K ⟶
      (ihom a).obj ((ihom ((ihom H).obj L)).obj K) :=
  ihomComp _ _ K ≫ (ihomMap (toIhomIhom a H L)).app _

/-- The twice uncurried form of `toIhomIhom`: `(x ⊗ y) ⊗ t ↦ y (t x)`. -/
lemma uncurryHom_toIhomIhom :
    uncurryHom (toIhomIhom a H L) ▷ ((ihom a).obj H).X ≫ evaluation ((ihom a).obj H) L =
      (β_ a.X ((ihom H).obj L).X).hom ▷ ((ihom a).obj H).X ≫
        (α_ _ _ _).hom ≫ ((ihom H).obj L).X ◁ ((β_ a.X _).hom ≫ evaluation a H) ≫
          evaluation H L := by
  rw [toIhomIhom, uncurryHom_comp, uncurryHom_transpose, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, uncurryHom_ihomComp, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left, comp_whiskerRight_assoc,
    associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← uncurryHom, uncurryHom_transpose, uncurryHom_id]

/-- The twice uncurried form of `ihomIhomComparison`: `(f ⊗ x) ⊗ y ↦ f (δ (x ⊗ y))`, where `δ`
is the uncurried form of `toIhomIhom`. -/
@[reassoc]
lemma uncurryHom_ihomIhomComparison :
    uncurryHom (ihomIhomComparison a H L K) ▷ ((ihom H).obj L).X ≫
        evaluation ((ihom H).obj L) K =
      (α_ _ _ _).hom ≫ _ ◁ uncurryHom (toIhomIhom a H L) ≫ evaluation _ K := by
  rw [ihomIhomComparison, uncurryHom_comp_ihomMap, comp_whiskerRight_assoc, uncurryHom_ihomComp,
    associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ← uncurryHom]

variable {a H L K} in
/-- The uncurried form of `toIhomIhom` is natural in `a`. -/
lemma uncurryHom_toIhomIhom_naturality {a' : Mod C A} (h : a' ⟶ a) :
    uncurryHom (toIhomIhom a' H L) ≫ ((ihomMap ((ihomMap h).app H)).app L).hom =
      h.hom ▷ ((ihom H).obj L).X ≫ uncurryHom (toIhomIhom a H L) := by
  apply hom_ext_of_evaluation (D := (ihom a).obj H)
  rw [comp_whiskerRight_assoc, evaluation_ihomMap, ← whisker_exchange_assoc,
    uncurryHom_toIhomIhom, comp_whiskerRight_assoc, uncurryHom_toIhomIhom, whisker_exchange_assoc,
    associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_right_assoc,
    evaluation_ihomMap, ← BraidedCategory.braiding_naturality_left_assoc,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left, comp_whiskerRight_assoc,
    associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]

variable {a} in
/-- `ihomIhomComparison` is natural in `a`. -/
lemma ihomIhomComparison_naturality {a' : Mod C A} (h : a' ⟶ a) :
    (ihomMap ((ihomMap ((ihomMap h).app H)).app L)).app K ≫ ihomIhomComparison a' H L K =
      ihomIhomComparison a H L K ≫ (ihomMap h).app _ := by
  apply hom_ext₂
  rw [uncurryHom_comp, comp_whiskerRight_assoc, uncurryHom_ihomIhomComparison,
    uncurryHom_comp_ihomMap, comp_whiskerRight_assoc, uncurryHom_ihomIhomComparison,
    associator_naturality_left_assoc, ← whisker_exchange_assoc, evaluation_ihomMap,
    associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, uncurryHom_toIhomIhom_naturality]

variable {K} in
/-- `ihomIhomComparison` is natural in `K`. -/
@[reassoc]
lemma ihomIhomComparison_naturality_right {K' : Mod C A} (f : K ⟶ K') :
    (ihom _).map f ≫ ihomIhomComparison a H L K' =
      ihomIhomComparison a H L K ≫ (ihom a).map ((ihom ((ihom H).obj L)).map f) := by
  apply hom_ext₂
  rw [uncurryHom_comp, comp_whiskerRight_assoc, uncurryHom_ihomIhomComparison,
    uncurryHom_comp_ihom_map, comp_whiskerRight_assoc, evaluation_naturality,
    uncurryHom_ihomIhomComparison_assoc, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, evaluation_naturality]

end Compare

/-- `Hom_A(f, -)` is an isomorphism for an isomorphism `f`. -/
instance isIso_ihomMap {M M' : Mod C A} (f : M ⟶ M') [IsIso f] : IsIso (ihomMap f) :=
  ⟨ihomMap (inv f), by rw [← ihomMap_comp, IsIso.inv_hom_id, ihomMap_id], by
    rw [← ihomMap_comp, IsIso.hom_inv_id, ihomMap_id]⟩

section Regular

omit [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)] in
/-- The unit `p ↦ p ⊗ 1` followed by the right action is the identity. -/
@[reassoc]
lemma rightUnitor_inv_whiskerLeft_unit_rightAct (M : Mod C A) :
    (ρ_ M.X).inv ≫ M.X ◁ η[A] ≫ rightAct M = 𝟙 _ := by
  have := congrArg Mod.Hom.hom (unitRight_rightActHom M)
  rw [Mod.comp_hom', Mod.id_hom'] at this
  change ((ρ_ M.X).inv ≫ M.X ◁ η[A]) ≫ rightAct M = 𝟙 _ at this
  simpa only [Category.assoc] using this

omit [MonObj A] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)] in
/-- Inserting a unit `u : 𝟙 ⟶ B` on the left of `E` and moving it to the right of `E` through
the braiding. -/
@[reassoc]
lemma unit_braiding_whiskerRight_associator {B : C} (u : 𝟙_ C ⟶ B) (E T : C) :
    ((λ_ E).inv ≫ u ▷ E ≫ (β_ B E).hom) ▷ T ≫ (α_ E B T).hom = E ◁ ((λ_ T).inv ≫ u ▷ T) := by
  rw [BraidedCategory.braiding_naturality_left, leftUnitor_inv_braiding_assoc,
    comp_whiskerRight_assoc, associator_naturality_middle, triangle_assoc_comp_right_inv_assoc,
    MonoidalCategory.whiskerLeft_comp]

/-- A morphism into `Hom_A(A, N)` followed by `Hom_A(A, N) ≅ N` is its uncurried form evaluated
at `1`. -/
lemma comp_ihomRegularIso_hom_app_hom {P N : Mod C A} (v : P ⟶ (ihom (regular A)).obj N) :
    (v ≫ ihomRegularIso.hom.app N).hom = (ρ_ P.X).inv ≫ P.X ◁ η[A] ≫ uncurryHom v := by
  rw [uncurryHom, evaluation_regular]
  change _ = (ρ_ P.X).inv ≫ P.X ◁ η[A] ≫ v.hom ▷ A ≫ (ihomRegularIso.hom.app N).hom ▷ A ≫ _
  rw [← comp_whiskerRight_assoc, ← Mod.comp_hom', whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]
  erw [rightUnitor_inv_whiskerLeft_unit_rightAct]
  rw [Category.comp_id]

/-- The evaluation of `Hom_A(A, H) ⊗ A ⟶ H` at `1`, written with the unit on the left, is the
isomorphism `Hom_A(A, H) ≅ H`. -/
lemma leftUnitor_inv_unit_braiding_evaluation (H : Mod C A) :
    (λ_ _).inv ≫ η[A] ▷ ((ihom (regular A)).obj H).X ≫ (β_ A _).hom ≫
        evaluation (regular A) H = (ihomRegularIso.hom.app H).hom := by
  rw [BraidedCategory.braiding_naturality_left_assoc, leftUnitor_inv_braiding_assoc,
    evaluation_regular]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  erw [rightUnitor_inv_whiskerLeft_unit_rightAct]
  rw [Category.comp_id]

variable (H L K : Mod C A)

/-- For `a = A` the uncurried form of `toIhomIhom`, evaluated at `1`, is the isomorphism
`Hom_A(H, L) ≅ Hom_A(Hom_A(A, H), L)`. -/
lemma leftUnitor_inv_unit_uncurryHom_toIhomIhom :
    (λ_ _).inv ≫ η[A] ▷ ((ihom H).obj L).X ≫ uncurryHom (toIhomIhom (regular A) H L) =
      ((ihomMap (ihomRegularIso.hom.app H)).app L).hom := by
  apply hom_ext_of_evaluation (D := (ihom (regular A)).obj H)
  rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc, uncurryHom_toIhomIhom,
    evaluation_ihomMap, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  rw [Category.assoc]
  erw [unit_braiding_whiskerRight_associator_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  exact congrArg (fun f ↦ ((ihom H).obj L).X ◁ f ≫ evaluation H L)
    ((Category.assoc _ _ _).trans (leftUnitor_inv_unit_braiding_evaluation H))

/-- For `a = A`, `ihomIhomComparison` is, up to `Hom_A(A, -) ≅ 𝟭`, induced by the isomorphism
`Hom_A(H, L) ≅ Hom_A(Hom_A(A, H), L)`. -/
lemma ihomIhomComparison_regular :
    ihomIhomComparison (regular A) H L K ≫ ihomRegularIso.hom.app _ =
      (ihomMap ((ihomMap (ihomRegularIso.hom.app H)).app L)).app K := by
  apply uncurryHom_injective
  conv_rhs => rw [uncurryHom]; erw [evaluation_ihomMap]
  rw [uncurryHom, comp_ihomRegularIso_hom_app_hom, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, uncurryHom_ihomIhomComparison]
  change _ ≫ (_ ◁ η[A]) ▷ _ ≫ (α_ _ A _).hom ≫ _ = _
  rw [associator_naturality_middle_assoc, triangle_assoc_comp_right_inv_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [Category.assoc, leftUnitor_inv_unit_uncurryHom_toIhomIhom]

/-- `ihomIhomComparison` is an isomorphism for `a = A`. -/
instance isIso_ihomIhomComparison_regular :
    IsIso (ihomIhomComparison (regular A) H L K) := by
  have : IsIso (ihomIhomComparison (regular A) H L K ≫ ihomRegularIso.hom.app _) := by
    rw [ihomIhomComparison_regular]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (ihomRegularIso.hom.app _)

end Regular

section Biproduct

attribute [local instance] Abelian.hasFiniteBiproducts

/-- `f ↦ Hom_A(f, N)` as an additive map. -/
noncomputable def ihomMapAppAddHom (M M' N : Mod C A) :
    (M ⟶ M') →+ ((ihom M').obj N ⟶ (ihom M).obj N) where
  toFun f := (ihomMap f).app N
  map_zero' := by
    have h := map_zero (ihomMapAddHom M M')
    change ihomMap 0 = 0 at h
    rw [h]
    rfl
  map_add' f g := by rw [ihomMap_add]; rfl

variable (H L K : Mod C A)

/-- The morphism `Hom_A(Hom_A(Hom_A(a, H), L), K) ⟶ Hom_A(Hom_A(Hom_A(a', H), L), K)` induced by
`h : a' ⟶ a`, as an additive map. -/
noncomputable def ihomIhomIhomMapAddHom (a' a : Mod C A) :
    (a' ⟶ a) →+ ((ihom ((ihom ((ihom a).obj H)).obj L)).obj K ⟶
      (ihom ((ihom ((ihom a').obj H)).obj L)).obj K) :=
  (ihomMapAppAddHom _ _ K).comp ((ihomMapAppAddHom _ _ L).comp (ihomMapAppAddHom a' a H))

/-- The value of `ihomIhomIhomMapAddHom`. -/
lemma ihomIhomIhomMapAddHom_apply {a' a : Mod C A} (h : a' ⟶ a) :
    ihomIhomIhomMapAddHom H L K a' a h =
      (ihomMap ((ihomMap ((ihomMap h).app H)).app L)).app K :=
  rfl

/-- `ihomIhomIhomMapAddHom` is contravariantly functorial. -/
lemma ihomIhomIhomMapAddHom_comp {a'' a' a : Mod C A} (g : a'' ⟶ a') (h : a' ⟶ a) :
    ihomIhomIhomMapAddHom H L K a'' a (g ≫ h) =
      ihomIhomIhomMapAddHom H L K a' a h ≫ ihomIhomIhomMapAddHom H L K a'' a' g := by
  simp only [ihomIhomIhomMapAddHom_apply, ihomMap_comp, NatTrans.comp_app]

/-- `ihomIhomIhomMapAddHom` preserves identities. -/
lemma ihomIhomIhomMapAddHom_id (a : Mod C A) :
    ihomIhomIhomMapAddHom H L K a a (𝟙 a) = 𝟙 _ := by
  simp only [ihomIhomIhomMapAddHom_apply, ihomMap_id, NatTrans.id_app]

/-- `ihomIhomComparison` is an isomorphism for `a` if it is one for a module isomorphic to
`a`. -/
lemma isIso_ihomIhomComparison_of_iso {a' a : Mod C A} (e : a' ≅ a)
    [IsIso (ihomIhomComparison a H L K)] : IsIso (ihomIhomComparison a' H L K) := by
  have h := ihomIhomComparison_naturality H L K e.hom
  have : IsIso ((ihomMap ((ihomMap ((ihomMap e.hom).app H)).app L)).app K) := inferInstance
  have : IsIso ((ihomMap ((ihomMap ((ihomMap e.hom).app H)).app L)).app K ≫
      ihomIhomComparison a' H L K) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((ihomMap ((ihomMap ((ihomMap e.hom).app H)).app L)).app K) _

/-- `ihomIhomComparison` is an isomorphism for a finite direct sum if it is one for each
summand. -/
lemma isIso_ihomIhomComparison_biproduct {n : ℕ} (M : Fin n → Mod C A)
    [∀ i, IsIso (ihomIhomComparison (M i) H L K)] :
    IsIso (ihomIhomComparison (⨁ M) H L K) := by
  refine ⟨∑ i, (ihomMap (biproduct.ι M i)).app _ ≫ inv (ihomIhomComparison (M i) H L K) ≫
    ihomIhomIhomMapAddHom H L K _ _ (biproduct.π M i), ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    have (i : Fin n) : ihomIhomComparison (⨁ M) H L K ≫ (ihomMap (biproduct.ι M i)).app _ ≫
        inv (ihomIhomComparison (M i) H L K) ≫
          ihomIhomIhomMapAddHom H L K _ _ (biproduct.π M i) =
        ihomIhomIhomMapAddHom H L K _ _ (biproduct.π M i ≫ biproduct.ι M i) := by
      rw [← reassoc_of% (ihomIhomComparison_naturality H L K (biproduct.ι M i)),
        IsIso.hom_inv_id_assoc, ihomIhomIhomMapAddHom_comp, ihomIhomIhomMapAddHom_apply]
      rfl
    simp_rw [this]
    rw [← map_sum, biproduct.total, ihomIhomIhomMapAddHom_id]
  · rw [Preadditive.sum_comp]
    have (i : Fin n) : ((ihomMap (biproduct.ι M i)).app _ ≫
        inv (ihomIhomComparison (M i) H L K) ≫
          ihomIhomIhomMapAddHom H L K _ _ (biproduct.π M i)) ≫ ihomIhomComparison (⨁ M) H L K =
        (ihomMap (biproduct.π M i ≫ biproduct.ι M i)).app _ := by
      rw [Category.assoc, Category.assoc, ihomIhomIhomMapAddHom_apply,
        ihomIhomComparison_naturality, IsIso.inv_hom_id_assoc, ihomMap_comp, NatTrans.comp_app]
    simp_rw [this]
    rw [← NatTrans.app_sum]
    have h := map_sum (ihomMapAddHom (⨁ M) (⨁ M)) (fun i ↦ biproduct.π M i ≫ biproduct.ι M i)
      Finset.univ
    simp only [ihomMapAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    rw [← h, biproduct.total, ihomMap_id]
    rfl

/-- `ihomIhomComparison` is an isomorphism for a free module of finite rank. -/
instance isIso_ihomIhomComparison_free (n : ℕ) :
    IsIso (ihomIhomComparison (⨁ fun _ : Fin n ↦ regular A) H L K) :=
  isIso_ihomIhomComparison_biproduct H L K _

end Biproduct

end CategoryTheory.Mod
