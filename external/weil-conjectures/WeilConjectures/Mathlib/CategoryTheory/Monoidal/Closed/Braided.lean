/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Invertible objects of braided monoidal categories

In a braided monoidal category, tensoring with an invertible object is an equivalence
(`CategoryTheory.IsInvertible.isEquivalence_tensorLeft`). Consequently:

* whiskering with an invertible object reflects isomorphisms
  (`CategoryTheory.IsInvertible.isIso_of_isIso_whiskerLeft`);
* in a closed category, the evaluation `A ⊗ [A, B] ⟶ B` of an invertible `A` is an isomorphism
  (`CategoryTheory.IsInvertible.isIso_ev`), and a conservative monoidal functor `G` whose
  comparison `G [A, 𝟙] ⟶ [G A, G 𝟙]` is an isomorphism reflects the invertibility of `A`
  (`CategoryTheory.isInvertible_of_isIso_ihomComparison`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C]

/-- In a braided monoidal category, tensoring on the left with an invertible object is an
equivalence: it is isomorphic, through the braiding, to tensoring on the right
(`CategoryTheory.tensorRightEquivalenceOfTensorIso`). -/
lemma IsInvertible.isEquivalence_tensorLeft {X : C} (hX : IsInvertible X) :
    (tensorLeft X).IsEquivalence := by
  obtain ⟨Z, ⟨e⟩, ⟨e'⟩⟩ := hX
  exact Functor.isEquivalence_of_iso (G := tensorLeft X)
    (F := (tensorRightEquivalenceOfTensorIso e e').functor)
    (NatIso.ofComponents (fun W ↦ (β_ X W).symm) fun f ↦ by
      change f ▷ X ≫ _ = _
      simp)

/-- Whiskering with an invertible object reflects isomorphisms. -/
lemma IsInvertible.isIso_of_isIso_whiskerLeft {W : C} (hW : IsInvertible W) {A B : C}
    (φ : A ⟶ B) [IsIso (W ◁ φ)] : IsIso φ := by
  have := hW.isEquivalence_tensorLeft
  have : IsIso ((tensorLeft W).map φ) := inferInstanceAs (IsIso (W ◁ φ))
  exact isIso_of_reflects_iso φ (tensorLeft W)

/-- The evaluation `A ⊗ [A, B] ⟶ B` of an invertible object `A` of a closed braided monoidal
category is an isomorphism: it is the counit of `tensorLeft A ⊣ ihom A`, whose left adjoint is an
equivalence. -/
lemma IsInvertible.isIso_ev [MonoidalClosed C] {A : C} (hA : IsInvertible A) (B : C) :
    IsIso ((ihom.ev A).app B) := by
  have := hA.isEquivalence_tensorLeft
  have : IsIso (ihom.adjunction A).counit := inferInstance
  exact NatIso.isIso_app_of_isIso (ihom.adjunction A).counit B

/-- **Invertibility is reflected by a conservative monoidal functor commuting with duals.** Let
`G` be a monoidal functor between closed braided monoidal categories which reflects isomorphisms,
and let `A` be an object for which the comparison `G [A, 𝟙] ⟶ [G A, G 𝟙]`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) is an isomorphism. If `G A` is invertible,
then so is `A`: `G` of the evaluation `A ⊗ [A, 𝟙] ⟶ 𝟙` is, up to the comparison and the
tensorator, the evaluation of the invertible object `G A`. -/
theorem isInvertible_of_isIso_ihomComparison [MonoidalClosed C] [BraidedCategory D]
    [MonoidalClosed D] (G : C ⥤ D) [G.Monoidal]
    (hG : ∀ {M N : C} (φ : M ⟶ N), IsIso (G.map φ) → IsIso φ) {A : C}
    [IsIso ((ihomComparison G A).app (𝟙_ C))] (h : IsInvertible (G.obj A)) :
    IsInvertible A := by
  have := h.isIso_ev (G.obj (𝟙_ C))
  have h₁ := ihomComparison_ev G A (𝟙_ C)
  have : IsIso (μ G A ((ihom A).obj (𝟙_ C)) ≫ G.map ((ihom.ev A).app (𝟙_ C))) := by
    rw [← h₁]
    infer_instance
  have := hG _ (IsIso.of_isIso_comp_left (μ G A ((ihom A).obj (𝟙_ C)))
    (G.map ((ihom.ev A).app (𝟙_ C))))
  exact (isInvertible_iff_of_braided A).2 ⟨_, ⟨asIso ((ihom.ev A).app (𝟙_ C))⟩⟩

end CategoryTheory
