/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.Mathlib.Order.BooleanAlgebra.Set

/-!
# WidePullbacks

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks`).
-/

@[expose] public section

namespace CategoryTheory.Limits

noncomputable
def WidePullback.reindex {α β : Type*} {C : Type*} [Category C] {B : C}
    {X : α → C} {Y : β → C}
    {f : (j : α) → X j ⟶ B} [HasWidePullback B X f]
    {g : (j : β) → Y j ⟶ B} [HasWidePullback B Y g]
    (e : α ≃ β) (s : ∀ a, X a ≅ Y (e a))
    (w : ∀ i, (s i).hom ≫ g (e i) = f _) :
    widePullback B X f ≅ widePullback B Y g where
  hom := WidePullback.lift (WidePullback.base _)
    (fun i ↦ WidePullback.π _ (e.symm i) ≫ (s _).hom ≫ eqToHom (by simp))
    fun i ↦ by
      obtain ⟨i, rfl⟩ := e.surjective i
      simp [w]
  inv := WidePullback.lift (WidePullback.base _)
    (fun i ↦ WidePullback.π _ (e i) ≫ (s _).inv)
    fun i ↦ by simp [← w]

noncomputable
def WidePullback.proj {α β : Type*} {C : Type*} [Category C] {B : C}
    {X : α ⊕ β → C}
    {f : (j : α ⊕ β) → X j ⟶ B} [HasWidePullback B X f]
    [HasWidePullback B (X ∘ Sum.inl) (fun j ↦ f (.inl j))] :
    widePullback B X f ⟶ widePullback B (X ∘ Sum.inl) (fun j ↦ f (.inl j)) :=
  WidePullback.lift (WidePullback.base _) (fun j ↦ WidePullback.π _ _) (by simp)

noncomputable
def WidePullback.mapOfSumEquiv {α β γ : Type*} {C : Type*} [Category C] {B : C}
    {X : α → C} {Y : β → C}
    {f : (j : α) → X j ⟶ B} [HasLimitsOfShape (WidePullbackShape α) C]
    {g : (j : β) → Y j ⟶ B} [HasLimitsOfShape (WidePullbackShape β) C]
    [HasLimitsOfShape (WidePullbackShape (β ⊕ γ)) C]
    (e : β ⊕ γ ≃ α) (s : ∀ (b : β), X (e (.inl b)) ⟶ Y b)
    (w : ∀ b, s b ≫ g b = f _) :
    widePullback B X f ⟶ widePullback B Y g :=
  (WidePullback.reindex (Y := X ∘ e) (g := fun i ↦ f (e i)) e.symm
    (fun a ↦ eqToIso (by simp)) (fun i ↦ by
      simp only [Function.comp_apply, eqToIso.hom]
      rw [← eqToHom_naturality, eqToHom_refl, Category.comp_id]
      rw [Equiv.apply_symm_apply])).hom ≫
    WidePullback.lift (objs := Sum.elim Y (X ∘ e ∘ .inr))
      (arrows := fun i ↦ match i with
        | .inl b => g b
        | .inr c => f _)
      (WidePullback.base _)
      (fun j ↦ match j with
        | .inl b => WidePullback.π _ _ ≫ s b
        | .inr b => WidePullback.π _ _)
      (by simp [w]) ≫
      WidePullback.proj

section

variable {C : Type*} [Category C]

namespace WidePullbackCone

variable {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}

theorem isPullback_sum {α β : Type*} {X : C} {Y : α ⊕ β → C}
    {f : ∀ i, Y i ⟶ X} (c : WidePullbackCone f)
    (cl : WidePullbackCone (fun i ↦ f (.inl i))) (cr : WidePullbackCone (fun i ↦ f (.inr i)))
    (hc : IsLimit c) (hcl : IsLimit cl) (hcr : IsLimit cr) :
    IsPullback
      (WidePullbackCone.IsLimit.lift hcl c.base (fun _ ↦ c.π _) (by simp))
      (WidePullbackCone.IsLimit.lift hcr c.base (fun _ ↦ c.π _) (by simp))
      cl.base cr.base := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_) ?_⟩⟩
  · refine WidePullbackCone.IsLimit.lift hc (s.fst ≫ cl.base) ?_ ?_
    · intro j
      match j with
      | .inl a => exact s.fst ≫ cl.π _
      | .inr a => exact s.snd ≫ cr.π _
    · rintro (_ | _) <;> simp [-PullbackCone.condition_one, s.condition.symm]
  · apply WidePullbackCone.IsLimit.hom_ext hcl <;> simp [-PullbackCone.condition_one]
  · apply WidePullbackCone.IsLimit.hom_ext hcr <;> simp [-PullbackCone.condition_one, s.condition]
  · intro s m h1 h2
    apply WidePullbackCone.IsLimit.hom_ext hc <;> simp [← h1, ← h2]

theorem isPullback_of_isCompl {α β γ : Type*} {X : C}
    {Y : γ → C} (f : ∀ i, Y i ⟶ X) (il : α → γ) (ir : β → γ)
    (hlr : IsCompl (Set.range il) (Set.range ir))
    (hil : il.Injective) (hir : ir.Injective)
    (c : WidePullbackCone f)
    (cl : WidePullbackCone fun i ↦ f (il i)) (cr : WidePullbackCone fun i ↦ f (ir i))
    (hc : IsLimit c) (hcl : IsLimit cl) (hcr : IsLimit cr) :
    IsPullback
      (WidePullbackCone.IsLimit.lift hcl c.base (fun i ↦ c.π (il i)) (by simp))
      (WidePullbackCone.IsLimit.lift hcr c.base (fun i ↦ c.π (ir i)) (by simp))
      cl.base cr.base := by
  have : Function.Surjective (Sum.elim il ir) := fun x ↦ by
    simp_rw [isCompl_iff, Set.codisjoint_iff, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ,
      forall_const] at hlr
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := hlr.2 x <;> simp
  let e : α ⊕ β ≃ γ :=
    .ofBijective (Sum.elim il ir) ⟨hil.sumElim hir (Set.disjoint_range_iff.mp hlr.1), this⟩
  let c' : WidePullbackCone (fun i ↦ f (e i)) := c.reindex e
  have hc' : IsLimit c' :=
    (WidePullbackCone.reindexIsLimitEquiv _ _).symm hc
  exact isPullback_sum c' cl cr hc' hcl hcr

lemma isPullback_of_isCompl' {α β : Type*} {X : C}
    {Y : β → C} (f : ∀ i, Y i ⟶ X) (l : α → β) (hl : Function.Injective l) (i : β)
    (H : IsCompl {i} (Set.range l)) (c : WidePullbackCone f) (hc : IsLimit c)
    (d : WidePullbackCone fun i ↦ f (l i)) (hd : IsLimit d) :
    IsPullback (c.π i)
      (WidePullbackCone.IsLimit.lift hd c.base (fun i ↦ c.π _) (by simp))
      (f i) d.base := by
  let γ := { j : β // i ≠ j }
  let cl : WidePullbackCone (fun _ : Unit ↦ f i) :=
    WidePullbackCone.mk (f i) (fun _ ↦ 𝟙 _) (by simp)
  have hcl : IsLimit cl := by
    refine WidePullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro t
      exact t.π ()
    · intro t
      simp [cl]
    · rintro t ⟨⟩
      exact Category.comp_id _
    · intro t m hm h
      exact (Category.comp_id m).symm.trans (h ())
  have key : c.π i = WidePullbackCone.IsLimit.lift hcl c.base (fun _ ↦ c.π i) (by simp) := by
    apply WidePullbackCone.IsLimit.hom_ext hcl
    · simp only [WidePullbackCone.IsLimit.lift_base]
      simp [cl]
    · intro j
      simp only [WidePullbackCone.IsLimit.lift_π]
      exact Category.comp_id _
  rw [key]
  exact c.isPullback_of_isCompl _ _ _ (by simpa)
    (Function.injective_of_subsingleton _) hl cl d hc hcl hd

lemma isPullback_ne {β : Type*} {X : C}
    {Y : β → C} (f : ∀ i, Y i ⟶ X) (i : β)
    [HasWidePullback X Y f] [HasWidePullback X (fun j : { j // i ≠ j } ↦ Y j) fun j ↦ f j] :
    IsPullback (WidePullback.π f _)
      (WidePullback.lift (WidePullback.base _) (fun j ↦ WidePullback.π _ _) (by simp))
      (f i) (WidePullback.base <| fun j : {j // i ≠ j } ↦ f j) := by
  apply isPullback_of_isCompl'
  · exact Subtype.val_injective
  · rw [isCompl_iff]
    simp [codisjoint_iff]
    grind
  · exact limit.isLimit _


end WidePullbackCone

end

end CategoryTheory.Limits
