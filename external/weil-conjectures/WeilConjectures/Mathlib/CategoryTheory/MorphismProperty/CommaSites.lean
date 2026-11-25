/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.CommaSites
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Continuity properties of functors between slices of a morphism property

## The localization functor preserves compatible families

The localization functor `MorphismProperty.Over.map ⊤ h` along `h : P f`, that is,
composition with `f : V ⟶ U`, preserves compatible families of elements for *any*
Grothendieck topology on `P.Over ⊤ U`
(`CategoryTheory.MorphismProperty.Over.compatiblePreserving_map`): the statement never
looks at the topology, only at the functor.

The proof is the cancellation property `P.HasOfPostcompProperty P` in action: a morphism
`f₁ : T' ⟶ (Over.map ⊤ h).obj Y₁` between `P`-schemes over `U` has `P f₁.left`, so the two
morphisms of a compatibility square over `U` are the images of morphisms of `P`-objects
over `V`, where the given family is compatible by assumption.

## Change of property preserves covers

For `P ≤ P'` and Grothendieck topologies `J ≤ J'` on `T`, the functor
`MorphismProperty.Over.changeProp X hPP' le_rfl : P.Over ⊤ X ⥤ P'.Over ⊤ X` preserves covers
for the topologies restricted from `J.over X` and `J'.over X` along the forgetful functors
(`CategoryTheory.MorphismProperty.Over.coverPreserving_changeProp`).
-/

@[expose] public section

set_option linter.style.show false

universe w v u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.MorphismProperty.Over

variable {T : Type u} [Category.{v} T] {P : MorphismProperty T}
  [P.IsMultiplicative] [P.HasOfPostcompProperty P]
  {V U : T} {f : V ⟶ U} (h : P f) (K : GrothendieckTopology (P.Over ⊤ U))

/-- The localization functor `MorphismProperty.Over.map ⊤ h` preserves compatible families
of elements, for an arbitrary Grothendieck topology `K` on `P.Over ⊤ U`. -/
lemma compatiblePreserving_map : CompatiblePreserving.{w} K (MorphismProperty.Over.map ⊤ h) where
  compatible := by
    intro ℱ Z S x hx Y₁ Y₂ T' f₁ f₂ g₁ g₂ hg₁ hg₂ hcomp
    have hleft : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := by
      have h' : (f₁ ≫ (MorphismProperty.Over.map ⊤ h).map g₁).left =
          (f₂ ≫ (MorphismProperty.Over.map ⊤ h).map g₂).left := by
        rw [hcomp]
      exact h'
    have hw : f₂.left ≫ Y₂.hom = f₁.left ≫ Y₁.hom := by
      have w₁ : g₁.left ≫ Z.hom = Y₁.hom := MorphismProperty.Over.w g₁
      have w₂ : g₂.left ≫ Z.hom = Y₂.hom := MorphismProperty.Over.w g₂
      rw [← w₁, ← w₂, ← Category.assoc, ← Category.assoc, hleft]
    -- `f₁.left` satisfies `P` since it is a morphism between `P`-objects over `U`.
    have hf₁P : P f₁.left := by
      apply P.of_postcomp (W' := P) f₁.left
        ((MorphismProperty.Over.map ⊤ h).obj Y₁).hom (MorphismProperty.Comma.prop _)
      rw [MorphismProperty.Over.w f₁]
      exact MorphismProperty.Comma.prop _
    let W' : P.Over ⊤ V := MorphismProperty.Over.mk ⊤ (f₁.left ≫ Y₁.hom)
      (P.comp_mem _ _ hf₁P Y₁.prop)
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk f₁.left rfl
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk f₂.left hw
    have hcomm : g₁' ≫ g₁ = g₂' ≫ g₂ := by
      apply MorphismProperty.Over.Hom.ext
      show f₁.left ≫ g₁.left = f₂.left ≫ g₂.left
      exact hleft
    have hT' : 𝟙 T'.left ≫ (f₁.left ≫ Y₁.hom) ≫ f = T'.hom := by
      simp only [Category.id_comp, Category.assoc]
      exact MorphismProperty.Over.w f₁
    let e : T' ⟶ (MorphismProperty.Over.map ⊤ h).obj W' :=
      MorphismProperty.Over.homMk (𝟙 T'.left) hT'
    have hf₁ : f₁ = e ≫ (MorphismProperty.Over.map ⊤ h).map g₁' := by
      apply MorphismProperty.Over.Hom.ext
      show f₁.left = 𝟙 T'.left ≫ f₁.left
      exact (Category.id_comp _).symm
    have hf₂ : f₂ = e ≫ (MorphismProperty.Over.map ⊤ h).map g₂' := by
      apply MorphismProperty.Over.Hom.ext
      show f₂.left = 𝟙 T'.left ≫ f₂.left
      exact (Category.id_comp _).symm
    have key := hx g₁' g₂' hg₁ hg₂ hcomm
    rw [hf₁, hf₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (ℱ.obj.map e.op) key

section ChangeProp

variable {P' : MorphismProperty T} {J J' : GrothendieckTopology T} (X : T)
  [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]

omit [P.IsMultiplicative] [P.HasOfPostcompProperty P] in
/-- For `P ≤ P'` and Grothendieck topologies `J ≤ J'`, the functor
`P.Over ⊤ X ⥤ P'.Over ⊤ X` preserves covers for the topologies restricted from `J.over X` and
`J'.over X` along the forgetful functors. -/
lemma coverPreserving_changeProp (hPP' : P ≤ P') (hJ : J ≤ J') :
    CoverPreserving ((Over.forget P ⊤ X).restrictedTopology (J.over X))
      ((Over.forget P' ⊤ X).restrictedTopology (J'.over X))
      (changeProp X hPP' (le_refl (⊤ : MorphismProperty T))) where
  cover_preserve {U R} hR := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    -- `changeProp X hPP' le_rfl ⋙ Over.forget P' ⊤ X` is `Over.forget P ⊤ X`
    rw [← Sieve.functorPushforward_comp]
    have hR' := Functor.mem_restrictedTopology_iff.mp hR
    rw [GrothendieckTopology.mem_over_iff] at hR' ⊢
    exact hJ _ hR'

end ChangeProp

end CategoryTheory.MorphismProperty.Over
