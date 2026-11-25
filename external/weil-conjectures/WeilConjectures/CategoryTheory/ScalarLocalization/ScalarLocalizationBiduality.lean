/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.Preadditive.Opposite
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationIso

/-! # Localization of a specified contravariant biduality isomorphism

Source: blueprint theorem-verdier-biduality--3, paragraph 1
(blueprint: lem-coef-scalar-localization-biduality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe r u v
open CategoryTheory Opposite TensorProduct
namespace CategoryTheory.ScalarLocalization

private theorem op_heq {C : Type*} [Category* C] {X Y X' Y' : C}
    (hx : X = X') (hy : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) :
    HEq f.op g.op := by
  cases hx
  cases hy
  cases h
  rfl

private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

/-- A specified integral biduality localizes to a natural biduality with exactly
its localized components, even when the localized dual's objects are only propositionally
identified with integral duals.
Source: blueprint theorem-verdier-biduality--3, paragraph 1
(blueprint: lem-coef-scalar-localization-biduality).
Proof: the double localized dual has the integral double-dual object by applying the
object equation twice. Its map on a pure tensor is the same scalar times the integral
double-dual map, by applying the contravariant pure-tensor formula twice. The existing
normalized localization theorem for natural isomorphisms applies to the integral
biduality and these two functors. Naturality extends from pure tensors to every arrow
by additivity. Components are prescribed by the integral biduality, including its inverse. -/
theorem biduality
    {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear R C] (t : R) (U : Cᵒᵖ ⥤ C)
    (F : (ScalarLocalization R C t)ᵒᵖ ⥤ ScalarLocalization R C t) [F.Additive]
    (ho : ∀ K : ScalarLocalization R C t,
      F.obj (op K) = (localization R C t).obj (U.obj (op K.obj)))
    (hm : ∀ (K M : C) (f : K ⟶ M) (c : Localization.Away t),
      HEq (F.map (Quiver.Hom.op (c ⊗ₜ[R] f : mk K ⟶ mk M)))
        (c ⊗ₜ[R] U.map f.op))
    (e : 𝟭 C ≅ U.rightOp ⋙ U) :
    ∃ b : 𝟭 (ScalarLocalization R C t) ≅ F.rightOp ⋙ F,
      ∀ K : ScalarLocalization R C t,
        HEq (b.hom.app K) ((localization R C t).map (e.hom.app K.obj)) := by
  let Q := localization R C t
  have hoo (K : ScalarLocalization R C t) :
      (F.rightOp ⋙ F).obj K = Q.obj ((U.rightOp ⋙ U).obj K.obj) := by
    exact (ho (F.obj (op K))).trans
      (congrArg (fun Z : ScalarLocalization R C t ↦ Q.obj (U.obj (op Z.obj))) (ho K))
  have hmm (K M : C) (f : K ⟶ M) (c : Localization.Away t) :
      HEq ((F.rightOp ⋙ F).map (c ⊗ₜ[R] f : mk K ⟶ mk M))
        (c ⊗ₜ[R] (U.rightOp ⋙ U).map f) := by
    have h₁ := map_heq F (congrArg op (ho (Q.obj K)))
      (congrArg op (ho (Q.obj M)))
      (op_heq (ho (Q.obj M)) (ho (Q.obj K)) (hm K M f c))
    exact h₁.trans (hm (U.obj (op M)) (U.obj (op K)) (U.map f.op) c)
  obtain ⟨b, hb, _⟩ := WeilConjectures.OperationsScalarLocalization.iso_existsUnique
    t t (fun x ↦ x) (𝟭 C) (U.rightOp ⋙ U) e
    (𝟭 (ScalarLocalization R C t)) (F.rightOp ⋙ F)
    (fun _ ↦ rfl) hoo (fun _ _ _ _ ↦ HEq.rfl) hmm
  exact ⟨b, hb⟩

end CategoryTheory.ScalarLocalization
