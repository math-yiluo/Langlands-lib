/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.CofilteredSystem

/-! # Transfer of stable images using finite comparisons

Source: Stacks Project, Tag 09C5, second proof paragraph; Tag 0594.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory Set
namespace CategoryTheory.Functor

/-- For each composable pair, there are bijections identifying its single-step and
composite images, with a common bijection at the target. They may vary with the pair.
Source: Stacks Tag 09C5, second proof paragraph.
(auxiliary; not a blueprint node). -/
def FiniteTripleRangeComparison {J : Type u} [Category J]
    (T : J ⥤ Type v) (U : J ⥤ Type w) : Prop :=
  ∀ ⦃n m t : J⦄ (f : m ⟶ n) (g : t ⟶ m),
    ∃ (en : T.obj n → U.obj n) (em : T.obj m → U.obj m)
      (et : T.obj t → U.obj t),
      Function.Bijective en ∧ Function.Bijective em ∧ Function.Bijective et ∧
      (∀ x, en (T.map f x) = U.map f (em x)) ∧
      ∀ x, en (T.map (g ≫ f) x) = U.map (g ≫ f) (et x)

/-- A finite-triple comparison with a Mittag–Leffler system suffices for stable images.
Source: Stacks Tags 09C5 and 0594.
(auxiliary; not a blueprint node).

Proof: choose a stabilizing arrow for U at n. For each further arrow, compare its
composite and the chosen arrow using one finite-triple marking. Transport the first
image to U, lift it through the composite using stabilization, and lift back by the
bijection at the furthest object. Injectivity of the common target marking identifies
the lifted image. The eventual-range criterion then proves Mittag–Leffler for T.
This argument allows empty sets, identity arrows and independent marking choices. -/
theorem isMittagLeffler_of_finiteTripleRangeComparison
    {J : Type u} [Category J] [IsCofilteredOrEmpty J]
    {T : J ⥤ Type v} {U : J ⥤ Type w}
    (h : FiniteTripleRangeComparison T U) (hU : U.IsMittagLeffler) : T.IsMittagLeffler := by
  apply (isMittagLeffler_iff_subset_range_comp T).2
  intro n
  obtain ⟨m, f, hf⟩ := (isMittagLeffler_iff_subset_range_comp U).1 hU n
  refine ⟨m, f, ?_⟩
  intro t g x hx
  obtain ⟨en, em, et, hen, _, het, hfirst, hcomp⟩ := h f g
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, hb⟩ := hf g ⟨em a, (hfirst a).symm⟩
  obtain ⟨c, hc⟩ := het.2 b
  refine ⟨c, hen.1 ?_⟩
  calc
    en (T.map (g ≫ f) c) = U.map (g ≫ f) (et c) := hcomp c
    _ = U.map (g ≫ f) b := congrArg _ hc
    _ = en (T.map f a) := hb

end CategoryTheory.Functor
