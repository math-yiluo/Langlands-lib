/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Invertibility of units along a mate

For an adjunction `L ⊣ R`, the unit `η_B : B ⟶ R (L B)` is invertible if and only if `L` is
bijective on morphisms with target `B`
(`CategoryTheory.Adjunction.isIso_unit_app_of_map_bijective`, converse to
`CategoryTheory.Adjunction.map_bijective_of_isIso_unit_app`).

Consider a square of functors with adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` along the top and
bottom, `G ⊣ G'` and `H ⊣ H'` along the sides, an isomorphism `α : G ⋙ L₂ ≅ L₁ ⋙ H` and its mate
`β : R₁ ⋙ G ⟶ H ⋙ R₂`. If `β` is invertible at `d` and the unit of `H ⊣ H'` is invertible at `d`,
then the unit of `G ⊣ G'` is invertible at `R₁ d`
(`CategoryTheory.isIso_unit_app_of_isIso_mateEquiv_app`). In algebraic geometry this says that
for a base change square for which base change holds, the full faithfulness of the pullback
along the base-changed morphism at `M` gives that of the pullback at the direct image of `M`.
-/

@[expose] public section

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}

/-- If `L` is bijective on morphisms with target `B`, then the unit `η_B` of `L ⊣ R` is an
isomorphism. -/
lemma isIso_unit_app_of_map_bijective (adj : L ⊣ R) (B : C)
    (h : ∀ A : C, Function.Bijective (L.map : (A ⟶ B) → (L.obj A ⟶ L.obj B))) :
    IsIso (adj.unit.app B) := by
  rw [isIso_iff_yoneda_map_bijective]
  intro A
  have e : (fun f : A ⟶ B ↦ f ≫ adj.unit.app B) =
      adj.homEquiv A (L.obj B) ∘ (L.map : (A ⟶ B) → (L.obj A ⟶ L.obj B)) := by
    funext f
    exact (homEquiv_map adj f).symm
  exact (congrArg Function.Bijective e).mpr ((adj.homEquiv _ _).bijective.comp (h A))

end Adjunction

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G' : E ⥤ C} {H' : F ⥤ D}

/-- Let `α : G ⋙ L₂ ⟶ L₁ ⋙ H` be an isomorphism, with mate `β : R₁ ⋙ G ⟶ H ⋙ R₂` for the
adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, and let `G ⊣ G'` and `H ⊣ H'`. If `β` and the unit of
`H ⊣ H'` are invertible at `d`, then the unit of `G ⊣ G'` is invertible at `R₁ d`. The square is
```
C --L₁--> D
|G        |H
v         v
E --L₂--> F
```
filled by `α`. Under the adjunctions, `G : (T ⟶ R₁ d) → (G T ⟶ G (R₁ d))` followed by `β_d` is
`H : (L₁ T ⟶ d) → (H (L₁ T) ⟶ H d)` followed by `α_T`. -/
theorem isIso_unit_app_of_isIso_mateEquiv_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adjG : G ⊣ G') (adjH : H ⊣ H') (α : TwoSquare G L₁ L₂ H) [IsIso α] (d : D)
    [IsIso ((mateEquiv adj₁ adj₂ α).app d)] [IsIso (adjH.unit.app d)] :
    IsIso (adjG.unit.app (R₁.obj d)) := by
  refine adjG.isIso_unit_app_of_map_bijective _ fun T ↦ ?_
  have e : (fun f : T ⟶ R₁.obj d ↦ G.map f ≫ (mateEquiv adj₁ adj₂ α).app d) =
      adj₂.homEquiv _ _ ∘ (fun x ↦ α.app T ≫ x) ∘ (H.map : (L₁.obj T ⟶ d) → _) ∘
        (adj₁.homEquiv T d).symm := by
    funext f
    apply (adj₂.homEquiv _ _).symm.injective
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc, mateEquiv_counit]
    have := α.naturality f
    simp only [Functor.comp_map] at this
    rw [reassoc_of% this]
  have hb : Function.Bijective
      (fun f : T ⟶ R₁.obj d ↦ G.map f ≫ (mateEquiv adj₁ adj₂ α).app d) :=
    (congrArg Function.Bijective e).mpr ((adj₂.homEquiv _ _).bijective.comp
      (((asIso α).app T).symm.homFromEquiv.bijective.comp
        ((adjH.map_bijective_of_isIso_unit_app _).comp (adj₁.homEquiv T d).symm.bijective)))
  have e' : (G.map : (T ⟶ R₁.obj d) → _) =
      (fun g ↦ g ≫ inv ((mateEquiv adj₁ adj₂ α).app d)) ∘
        (fun f : T ⟶ R₁.obj d ↦ G.map f ≫ (mateEquiv adj₁ adj₂ α).app d) := by
    funext f
    simp
  exact (congrArg Function.Bijective e').mpr
    ((asIso ((mateEquiv adj₁ adj₂ α).app d)).symm.homToEquiv.bijective.comp hb)

end CategoryTheory
