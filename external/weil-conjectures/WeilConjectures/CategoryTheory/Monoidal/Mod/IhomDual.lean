/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry
public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing

/-!
# The morphism `M ⊗ N ⟶ Hom_A(Hom_A(M, A), N)`

Let `A` be a commutative monoid in a braided monoidal Grothendieck abelian category `C`. For
`A`-modules `M` and `N` we construct the morphism
`M ⊗ N ⟶ Hom_A(M^∨, N)`, `m ⊗ n ↦ (φ ↦ φ(m) n)`, where `M^∨ = Hom_A(M, A)`
(`CategoryTheory.Mod.toIhomDual`), characterised by its uncurried form
`(m ⊗ n) ⊗ φ ↦ φ(m) n` (`CategoryTheory.Mod.toIhomDual_evaluation`).

For a lax monoidal functor `Φ : C ⥤ ModuleCat R` compatible with the braidings, the induced
pairing satisfies `⟨Φ(m ⊗ n), φ⟩ = ⟨φ, m⟩ • n`
(`CategoryTheory.Mod.evaluationPairing_toIhomDual`).
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

variable (M N : Mod C A)

/-- The morphism `(M ⊗ N) ⊗ M^∨ ⟶ N`, `(m ⊗ n) ⊗ φ ↦ φ(m) n`. -/
noncomputable def toIhomDualAux :
    (M.X ⊗ N.X) ⊗ ((ihom M).obj (regular A)).X ⟶ N.X :=
  (β_ (M.X ⊗ N.X) ((ihom M).obj (regular A)).X).hom ≫ (α_ _ M.X N.X).inv ≫
    evaluation M (regular A) ▷ N.X ≫ act (A := A) N.X

/-- The morphism `(m ⊗ n) ⊗ φ ↦ φ(m) n` is `A`-linear in `φ`. -/
lemma isLinearRight_toIhomDualAux : IsLinearRight (toIhomDualAux M N) := by
  unfold IsLinearRight toIhomDualAux
  rw [BraidedCategory.braiding_naturality_right_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, act_whiskerRight_evaluation,
    BraidedCategory.braiding_tensor_right_hom]
  simp only [comp_whiskerRight, Category.assoc]
  erw [mul_act (A := A) N.X]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- The morphism `M ⊗ N ⟶ Hom_A(Hom_A(M, A), N)`, `m ⊗ n ↦ (φ ↦ φ(m) n)`. -/
noncomputable def toIhomDual :
    M.X ⊗ N.X ⟶ ((ihom ((ihom M).obj (regular A))).obj N).X :=
  curry (toIhomDualAux M N) (isLinearRight_toIhomDualAux M N)

/-- The uncurried form of `M ⊗ N ⟶ Hom_A(M^∨, N)` is `(m ⊗ n) ⊗ φ ↦ φ(m) n`. -/
lemma toIhomDual_evaluation :
    toIhomDual M N ▷ ((ihom M).obj (regular A)).X ≫ evaluation ((ihom M).obj (regular A)) N =
      toIhomDualAux M N :=
  curry_evaluation _ _

section Pairing

variable {R : Type w} [CommRing R] (Φ : C ⥤ ModuleCat.{w} R) [Φ.LaxMonoidal]

/-- **The pairing of `m ⊗ n` with `φ` is `φ(m) n`.** For a lax monoidal functor
`Φ : C ⥤ ModuleCat R` compatible with the braidings, the evaluation pairing of the image of
`m ⊗ n` under `M ⊗ N ⟶ Hom_A(M^∨, N)` with `φ` is the action of the pairing of `φ` and `m` on
`n`. -/
lemma evaluationPairing_toIhomDual
    (hΦ : ∀ X Y : C, μ Φ X Y ≫ Φ.map (β_ X Y).hom = (β_ (Φ.obj X) (Φ.obj Y)).hom ≫ μ Φ Y X)
    (m : Φ.obj M.X) (n : Φ.obj N.X) (φ : Φ.obj ((ihom M).obj (regular A)).X) :
    evaluationPairing Φ ((ihom M).obj (regular A)) N
        ((Φ.map (toIhomDual M N)).hom ((μ Φ M.X N.X).hom (m ⊗ₜ n))) φ =
      (Φ.map (act N.X)).hom ((μ Φ A N.X).hom (evaluationPairing Φ M (regular A) φ m ⊗ₜ n)) := by
  rw [evaluationPairing_apply, evaluationPairing_apply]
  have h₁ := congrArg (fun f ↦ f.hom ((μ Φ M.X N.X).hom (m ⊗ₜ n) ⊗ₜ φ))
    (μ_natural_left Φ (toIhomDual M N) ((ihom M).obj (regular A)).X)
  have h₂ := congrArg (fun f ↦ f.hom ((μ Φ M.X N.X).hom (m ⊗ₜ n) ⊗ₜ φ))
    (hΦ (M.X ⊗ N.X) ((ihom M).obj (regular A)).X)
  have h₃ := congrArg (fun f ↦ f.hom (φ ⊗ₜ (m ⊗ₜ n)))
    (associativity_inv Φ ((ihom M).obj (regular A)).X M.X N.X)
  have h₄ := congrArg (fun f ↦ f.hom ((μ Φ _ M.X).hom (φ ⊗ₜ m) ⊗ₜ n))
    (μ_natural_left Φ (evaluation M (regular A)) N.X)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply] at h₁ h₂ h₃ h₄
  erw [h₁]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, toIhomDual_evaluation, toIhomDualAux]
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [h₂, h₃, h₄]
  rfl

end Pairing

end CategoryTheory.Mod
