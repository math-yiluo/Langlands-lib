/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Mates computed through other right adjoints

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions and `α : G ⋙ L₂ ⟶ L₁ ⋙ H` a 2-square. If `L₁` and
`L₂` have other, explicit, right adjoints `F₁` and `F₂`, and a family `c_K : G F₁ K ⟶ F₂ H K` is
compatible with `α` and the counits of `L₁ ⊣ F₁` and `L₂ ⊣ F₂`, then the mate
`R₁ ⋙ G ⟶ H ⋙ R₂` of `α` is `c` read through the identifications `F₁ ≅ R₁` and `F₂ ≅ R₂` of
right adjoints. In particular it is an isomorphism at `K` when `c_K` is one.

This is how a base change map of exceptional inverse images, defined as a mate, is shown to be
invertible from an explicit description of the right adjoints and of their counits, compatible
with base change.

## Main statements

- `CategoryTheory.mateEquiv_app_eq_of_counit`
- `CategoryTheory.isIso_mateEquiv_app_of_counit`
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
variable {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ F₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ F₂ : D ⥤ C}

/-- The mate of a 2-square `α : G ⋙ L₂ ⟶ L₁ ⋙ H` under `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, computed through
other right adjoints `L₁ ⊣ F₁` and `L₂ ⊣ F₂`: if `c_K : G F₁ K ⟶ F₂ H K` satisfies
`L₂(c_K) ≫ ε₂ = α ≫ H(ε₁)` for the counits of `L₁ ⊣ F₁` and `L₂ ⊣ F₂`, then the mate at `K` is
`c_K` conjugated by the identifications `R₁ ≅ F₁` and `F₂ ≅ R₂`. -/
lemma mateEquiv_app_eq_of_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adjF₁ : L₁ ⊣ F₁)
    (adjF₂ : L₂ ⊣ F₂) (α : TwoSquare G L₁ L₂ H) (K : B)
    (c : G.obj (F₁.obj K) ⟶ F₂.obj (H.obj K))
    (hc : L₂.map c ≫ adjF₂.counit.app (H.obj K) = α.app (F₁.obj K) ≫ H.map (adjF₁.counit.app K)) :
    (mateEquiv adj₁ adj₂ α).app K = G.map ((Adjunction.rightAdjointUniq adj₁ adjF₁).hom.app K) ≫
      c ≫ (Adjunction.rightAdjointUniq adjF₂ adj₂).hom.app (H.obj K) := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, mateEquiv_counit, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc,
    Adjunction.rightAdjointUniq_hom_app_counit, hc]
  have := α.naturality ((Adjunction.rightAdjointUniq adj₁ adjF₁).hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at this
  rw [reassoc_of% this, ← Functor.map_comp, Adjunction.rightAdjointUniq_hom_app_counit]

/-- The mate of a 2-square `α : G ⋙ L₂ ⟶ L₁ ⋙ H` under `L₁ ⊣ R₁` and `L₂ ⊣ R₂` is an isomorphism
at `K` as soon as, for other right adjoints `L₁ ⊣ F₁` and `L₂ ⊣ F₂`, some isomorphism
`c_K : G F₁ K ⟶ F₂ H K` satisfies `L₂(c_K) ≫ ε₂ = α ≫ H(ε₁)` for their counits. -/
lemma isIso_mateEquiv_app_of_counit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adjF₁ : L₁ ⊣ F₁)
    (adjF₂ : L₂ ⊣ F₂) (α : TwoSquare G L₁ L₂ H) (K : B)
    (c : G.obj (F₁.obj K) ⟶ F₂.obj (H.obj K)) [IsIso c]
    (hc : L₂.map c ≫ adjF₂.counit.app (H.obj K) = α.app (F₁.obj K) ≫ H.map (adjF₁.counit.app K)) :
    IsIso ((mateEquiv adj₁ adj₂ α).app K) := by
  rw [mateEquiv_app_eq_of_counit adj₁ adj₂ adjF₁ adjF₂ α K c hc]
  infer_instance

end CategoryTheory
