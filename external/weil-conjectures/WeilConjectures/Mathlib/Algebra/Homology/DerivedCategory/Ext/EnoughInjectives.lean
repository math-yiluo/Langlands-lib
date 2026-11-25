/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Comparing `Ext`-groups by dimension shifting

Let `X` be an object of an abelian category and `0 → S.X₁ → S.X₂ → S.X₃ → 0` a short exact
sequence. If `S.X₂` has no `Ext¹` from `X`, then `Ext¹(X, S.X₁)` vanishes exactly when every
morphism `X ⟶ S.X₃` lifts to `S.X₂`; if `S.X₂` has no `Ext` from `X` in degrees `n + 1` and
`n + 2`, then `Ext^{n + 2}(X, S.X₁)` vanishes exactly when `Ext^{n + 1}(X, S.X₃)` does.

Combining the two along injective resolutions compares `Ext`-groups computed in two different
abelian categories. Let `Φ : C ⥤ D` be an exact functor, `P : C` and `Z : D`, such that `Φ` sends
the injective objects of `C` to objects without higher `Ext` from `Z`, and such that the
vanishing of `Ext¹(Z, Φ S.X₁)` for a short exact sequence `S` with injective middle term lets
morphisms `P ⟶ S.X₃` lift to `S.X₂`. Then `Ext^{n + 1}(P, F) = 0` as soon as
`Ext^{n + 1}(Z, Φ F) = 0` (`CategoryTheory.Abelian.Ext.subsingleton_of_subsingleton_map`). This is
how the cohomology of a sheaf of modules is compared with the cohomology of its underlying
abelian sheaf.

## Main statements

- `CategoryTheory.Abelian.Ext.subsingleton_one_iff_surjective`: the degree-one criterion.
- `CategoryTheory.Abelian.Ext.subsingleton_succ_succ_iff`: dimension shifting.
- `CategoryTheory.Abelian.Ext.subsingleton_of_subsingleton_map`: the comparison.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Abelian.Ext

open Limits

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **The degree-one criterion.** For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` such
that `Ext¹(X, S.X₂) = 0`, the group `Ext¹(X, S.X₁)` vanishes if and only if every morphism
`X ⟶ S.X₃` lifts along `S.g`. -/
lemma subsingleton_one_iff_surjective (X : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext.{w} X S.X₂ 1)] :
    Subsingleton (Ext.{w} X S.X₁ 1) ↔ Function.Surjective (fun f : X ⟶ S.X₂ ↦ f ≫ S.g) := by
  constructor
  · intro _ q
    obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ X hS (mk₀ q) (zero_add 1)
      (Subsingleton.elim _ _)
    obtain ⟨f, rfl⟩ := addEquiv₀.symm.surjective x₂
    refine ⟨f, (mk₀_bijective _ _).1 ?_⟩
    rw [← hx₂]
    exact (mk₀_comp_mk₀ f S.g).symm
  · intro h
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ X hS x (Subsingleton.elim _ _) (zero_add 1)
    obtain ⟨q, rfl⟩ := addEquiv₀.symm.surjective y
    obtain ⟨f, rfl⟩ := h q
    change (mk₀ (f ≫ S.g)).comp hS.extClass _ = 0
    rw [← mk₀_comp_mk₀, comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      hS.comp_extClass, comp_zero]

/-- **Dimension shifting.** For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` such that
`S.X₂` has no `Ext` from `X` in degrees `n + 1` and `n + 2`, the group `Ext^{n + 2}(X, S.X₁)`
vanishes if and only if `Ext^{n + 1}(X, S.X₃)` does. -/
lemma subsingleton_succ_succ_iff (X : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext.{w} X S.X₂ (n + 1))] [Subsingleton (Ext.{w} X S.X₂ (n + 2))] :
    Subsingleton (Ext.{w} X S.X₁ (n + 2)) ↔ Subsingleton (Ext.{w} X S.X₃ (n + 1)) := by
  constructor
  · intro _
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₃ X hS x rfl (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, zero_comp]
  · intro _
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ X hS x (Subsingleton.elim _ _) rfl
    rw [Subsingleton.elim y 0, zero_comp]

end

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

/-- **Comparing `Ext`-groups along an exact functor.** Let `Φ : C ⥤ D` be an additive functor
between abelian categories which preserves short exact sequences, `C` having enough injectives,
and let `P : C` and `Z : D`. Assume that

* `Φ` sends injective objects of `C` to objects without higher `Ext` from `Z`;
* for every short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` in `C` with `S.X₂` injective and
  `Ext¹(Z, Φ S.X₁) = 0`, every morphism `P ⟶ S.X₃` lifts along `S.g`.

Then `Ext^{n + 1}(P, F) = 0` as soon as `Ext^{n + 1}(Z, Φ F) = 0`. The proof embeds `F` into an
injective object and shifts dimensions on both sides. -/
theorem subsingleton_of_subsingleton_map (Φ : C ⥤ D) [Φ.Additive]
    (hΦex : ∀ (S : ShortComplex C), S.ShortExact → (S.map Φ).ShortExact) (P : C) (Z : D)
    (hΦ : ∀ (I : C) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} Z (Φ.obj I) (n + 1)))
    (hsurj : ∀ (S : ShortComplex C), S.ShortExact → Injective S.X₂ →
      Subsingleton (Ext.{w'} Z (Φ.obj S.X₁) 1) →
        Function.Surjective (fun f : P ⟶ S.X₂ ↦ f ≫ S.g))
    (n : ℕ) (F : C) (hF : Subsingleton (Ext.{w'} Z (Φ.obj F) (n + 1))) :
    Subsingleton (Ext.{w} P F (n + 1)) := by
  induction n generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have : Subsingleton (Ext.{w} P S.X₂ 1) := subsingleton_of_injective _ _ 0
    exact (subsingleton_one_iff_surjective P hS).2 (hsurj S hS inferInstance hF)
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hS' : (S.map Φ).ShortExact := hΦex S hS
    have : Subsingleton (Ext.{w} P S.X₂ (n + 1)) := subsingleton_of_injective _ _ n
    have : Subsingleton (Ext.{w} P S.X₂ (n + 2)) := subsingleton_of_injective _ _ (n + 1)
    have : Subsingleton (Ext.{w'} Z (S.map Φ).X₂ (n + 1)) := hΦ S.X₂ n
    have : Subsingleton (Ext.{w'} Z (S.map Φ).X₂ (n + 2)) := hΦ S.X₂ (n + 1)
    have hQ : Subsingleton (Ext.{w'} Z (Φ.obj S.X₃) (n + 1)) :=
      (subsingleton_succ_succ_iff Z hS' n).1 hF
    exact (subsingleton_succ_succ_iff P hS n).2 (ih S.X₃ hQ)

end CategoryTheory.Abelian.Ext
