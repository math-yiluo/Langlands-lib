/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The sheaf condition for a single morphism

This file collects elementary facts about the sheaf condition `Presieve.IsSheafFor P (.singleton π)`
of a presheaf of types for a single morphism `π : T' ⟶ T`:

- `CategoryTheory.Presieve.isSheafFor_singleton_of_isPullback`: the sheaf condition for `π` is
  local on `T`: it follows from the sheaf condition for a morphism `c : T₁ ⟶ T`, for the base
  changes of `c` and `π` along each other, and for the base change of `π` to `T₁ ×_T T₁`.
- `CategoryTheory.Presieve.isSheafFor_singleton_overMap`: the sheaf condition for the image of a
  morphism under `Over.map` follows from the sheaf condition of the restricted presheaf.
- `CategoryTheory.Presieve.isSheafFor_singleton_of_injective`: the sheaf condition passes to a
  subpresheaf whose sections are detected after pulling back along `π`.
- `CategoryTheory.Presieve.mem_range_of_imageSieve_mem`: a section of a sheaf which lies locally
  in the image of an injective morphism from a sheaf lies in its image.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Presieve

open Opposite Limits

variable {C : Type u} [Category.{v} C] {P : Cᵒᵖ ⥤ Type w}

/-- The pullback of an element along `π` determines it, if `P` is a sheaf for `π`. -/
lemma IsSheafFor.injective_map_singleton {T T' : C} {π : T' ⟶ T}
    (h : IsSheafFor P (.singleton π)) : Function.Injective (P.map π.op) := by
  intro a b hab
  have H := isSheafFor_singleton.1 h (P.map π.op a) (fun p₁ p₂ hp ↦ by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hp])
  exact H.unique rfl hab.symm

/-- **The sheaf condition for a single morphism is local.** Let `π : T' ⟶ T` and `c : T₁ ⟶ T`,
let `π₁ : T₁' ⟶ T₁` be the base change of `π` along `c` and `c' : T₁' ⟶ T'` that of `c` along
`π`, let `d₁ d₂ : T₂ ⟶ T₁` be the projections of `T₂ = T₁ ×_T T₁` and `π₂ : T₂' ⟶ T₂` the base
change of `π` to `T₂`. If `P` is a sheaf for `c`, `c'`, `π₁` and `π₂`, it is a sheaf for `π`. -/
lemma isSheafFor_singleton_of_isPullback {T T' T₁ T₁' T₂ T₂' : C} (π : T' ⟶ T) (c : T₁ ⟶ T)
    (c' : T₁' ⟶ T') (π₁ : T₁' ⟶ T₁) (h₁ : IsPullback c' π₁ π c) (d₁ d₂ : T₂ ⟶ T₁)
    (hd : IsPullback d₁ d₂ c c) (e : T₂' ⟶ T') (π₂ : T₂' ⟶ T₂) (h₂ : IsPullback e π₂ π (d₁ ≫ c))
    (hc : IsSheafFor P (.singleton c)) (hc' : IsSheafFor P (.singleton c'))
    (hπ₁ : IsSheafFor P (.singleton π₁)) (hπ₂ : IsSheafFor P (.singleton π₂)) :
    IsSheafFor P (.singleton π) := by
  rw [isSheafFor_singleton]
  intro x hx
  -- restrict `x` to `T₁'` and descend it to `T₁`
  obtain ⟨y₁, hy₁, -⟩ := isSheafFor_singleton.1 hπ₁ (P.map c'.op x) (fun p₁ p₂ hp ↦ by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    exact hx _ _ (by rw [Category.assoc, Category.assoc, h₁.w, reassoc_of% hp]))
  -- the two pullbacks of `y₁` to `T₂` agree
  have hy₁d : P.map d₁.op y₁ = P.map d₂.op y₁ := by
    apply hπ₂.injective_map_singleton
    obtain ⟨l₁, hl₁, hl₁'⟩ : ∃ l, l ≫ c' = e ∧ l ≫ π₁ = π₂ ≫ d₁ :=
      ⟨_, h₁.lift_fst _ _ (by rw [h₂.w, Category.assoc]),
        h₁.lift_snd _ _ (by rw [h₂.w, Category.assoc])⟩
    obtain ⟨l₂, hl₂, hl₂'⟩ : ∃ l, l ≫ c' = e ∧ l ≫ π₁ = π₂ ≫ d₂ :=
      ⟨_, h₁.lift_fst _ _ (by rw [h₂.w, Category.assoc, hd.w]),
        h₁.lift_snd _ _ (by rw [h₂.w, Category.assoc, hd.w])⟩
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ← hl₁', ← hl₂',
      op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hy₁,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hl₁, hl₂]
  obtain ⟨y, hy, -⟩ := isSheafFor_singleton.1 hc y₁ (fun p₁ p₂ hp ↦ by
    obtain ⟨l, hl, hl'⟩ : ∃ l, l ≫ d₁ = p₁ ∧ l ≫ d₂ = p₂ :=
      ⟨_, hd.lift_fst _ _ hp, hd.lift_snd _ _ hp⟩
    rw [← hl, ← hl', op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hy₁d])
  have hyx : P.map π.op y = x := hc'.injective_map_singleton (by
    rw [← Functor.map_comp_apply, ← op_comp, h₁.w, op_comp, Functor.map_comp_apply, hy, hy₁])
  refine ⟨y, hyx, fun y' hy' ↦ hc.injective_map_singleton (hπ₁.injective_map_singleton ?_)⟩
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← h₁.w, op_comp,
    Functor.map_comp_apply, Functor.map_comp_apply, hy', hyx]

/-- If a presheaf `A` is a sheaf for `π` and `β : P ⟶ A` is injective on sections, then `P` is a
sheaf for `π` as soon as a section of `A` over `T` whose pullback along `π` comes from `P` comes
from `P` itself. -/
lemma isSheafFor_singleton_of_injective {A : Cᵒᵖ ⥤ Type w} (β : P ⟶ A) {T T' : C}
    {π : T' ⟶ T} (hβ : ∀ U, Function.Injective (β.app U)) (hA : IsSheafFor A (.singleton π))
    (himage : ∀ s : A.obj (op T), A.map π.op s ∈ Set.range (β.app (op T')) →
      s ∈ Set.range (β.app (op T))) :
    IsSheafFor P (.singleton π) := by
  rw [isSheafFor_singleton]
  intro x hx
  obtain ⟨s, hs, -⟩ := isSheafFor_singleton.1 hA (β.app _ x) (fun p₁ p₂ hp ↦ by
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hx _ _ hp])
  obtain ⟨u, rfl⟩ := himage s ⟨x, hs.symm⟩
  refine ⟨u, hβ _ ?_, fun u' hu' ↦ hβ _ (hA.injective_map_singleton ?_)⟩
  · rw [NatTrans.naturality_apply, hs]
  · rw [← NatTrans.naturality_apply, hu', ← hs]

/-- The sheaf condition for `Over.map p` applied to a morphism follows from the sheaf condition
of the restricted presheaf `(Over.map p).op ⋙ P`. -/
lemma isSheafFor_singleton_overMap {X Y : C} (p : X ⟶ Y) {P : (Over Y)ᵒᵖ ⥤ Type w}
    {A B : Over X} (g : A ⟶ B) (h : IsSheafFor ((Over.map p).op ⋙ P) (.singleton g)) :
    IsSheafFor P (.singleton ((Over.map p).map g)) := by
  rw [isSheafFor_singleton] at h ⊢
  intro x hx
  exact h x (fun p₁ p₂ hp ↦ hx _ _ (by simp only [← Functor.map_comp, Quiver.Hom.unop_op, hp]))


/-- A section `s` of a sheaf `A` which lies locally in the image of a morphism `β : P ⟶ A` from a
sheaf `P` which is injective on sections lies in the image of `β`. -/
lemma mem_range_of_imageSieve_mem (J : GrothendieckTopology C) {A : Cᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf J P) (hA : Presieve.IsSheaf J A) (β : P ⟶ A)
    (hβ : ∀ U, Function.Injective (β.app U)) {T : C} (s : A.obj (op T))
    (h : Presheaf.imageSieve β s ∈ J T) : s ∈ Set.range (β.app (op T)) := by
  classical
  let x : FamilyOfElements P (Presheaf.imageSieve β s).arrows := fun _ f hf ↦ hf.choose
  have hx {Z : C} (f : Z ⟶ T) (hf : Presheaf.imageSieve β s f) :
      β.app _ (x f hf) = A.map f.op s := hf.choose_spec
  have hcomp : x.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hg ↦ hβ _ (by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hx, hx, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hg])
  let u := (hP _ h).amalgamate x hcomp
  refine ⟨u, (hA _ h).isSeparatedFor.ext fun Z f hf ↦ ?_⟩
  rw [← NatTrans.naturality_apply, (hP _ h).valid_glue hcomp f hf, hx]

end CategoryTheory.Presieve
