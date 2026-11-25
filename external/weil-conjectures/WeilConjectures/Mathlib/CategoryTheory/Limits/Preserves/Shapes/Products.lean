/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The comparison map for coproducts

Properties of the comparison map `sigmaComparison F X : ∐ F(Xⱼ) ⟶ F(∐ Xⱼ)`.

## Main statements

- `CategoryTheory.Limits.sigmaComparison_comp`: the comparison map of a composite.
- `CategoryTheory.Limits.isIso_sigmaComparison_of_natIso`: invariance under natural isomorphism.
- `CategoryTheory.Limits.isIso_sigmaComparison_of_isZero`: the case of a functor with zero values.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {A B E : Type*} [Category* A] [Category* B] [Category* E]

/-- The comparison map of a composite `F ⋙ G` factors through the comparison maps of `G` and `F`:
```
∐ G(F Xⱼ) ──sigmaComparison G (F ∘ X)──▶ G(∐ F Xⱼ)
     │                                       │
     │ sigmaComparison (F ⋙ G) X             │ G.map (sigmaComparison F X)
     ▼                                       ▼
G(F(∐ Xⱼ)) ═════════════════════════════ G(F(∐ Xⱼ))
```
-/
lemma sigmaComparison_comp (F : A ⥤ B) (G : B ⥤ E) {J : Type*} (X : J → A)
    [HasCoproduct X] [HasCoproduct fun j ↦ F.obj (X j)]
    [HasCoproduct fun j ↦ (F ⋙ G).obj (X j)] [HasCoproduct fun j ↦ G.obj (F.obj (X j))] :
    sigmaComparison (F ⋙ G) X =
      sigmaComparison G (fun j ↦ F.obj (X j)) ≫ G.map (sigmaComparison F X) := by
  ext j
  dsimp only [sigmaComparison]
  simp [← G.map_comp]

/-- The comparison map for coproducts is an isomorphism for a functor isomorphic to one for which
it is. -/
lemma isIso_sigmaComparison_of_natIso {F F' : A ⥤ B} (e : F ≅ F') {J : Type*} (X : J → A)
    [HasCoproduct X] [HasCoproduct fun j ↦ F.obj (X j)] [HasCoproduct fun j ↦ F'.obj (X j)]
    [IsIso (sigmaComparison F X)] : IsIso (sigmaComparison F' X) :=
  have := PreservesCoproduct.of_iso_comparison F X
  have : PreservesColimit (Discrete.functor X) F' := preservesColimit_of_natIso _ e
  inferInstance

/-- The comparison map for coproducts is an isomorphism for a functor with zero values. -/
lemma isIso_sigmaComparison_of_isZero [HasZeroMorphisms B] [HasZeroObject B] (F : A ⥤ B)
    {J : Type*} (X : J → A) [HasCoproduct X] [HasCoproduct fun j ↦ F.obj (X j)]
    (hF : ∀ Y, IsZero (F.obj Y)) : IsIso (sigmaComparison F X) :=
  have h : IsZero (∐ fun j ↦ F.obj (X j)) :=
    (coproductIsCoproduct _).isZero_pt (Functor.isZero _ fun _ ↦ hF _)
  ⟨0, h.eq_of_src _ _, (hF _).eq_of_src _ _⟩

end CategoryTheory.Limits
