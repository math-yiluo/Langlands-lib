/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor

/-!
# The full long exact sequence of right derived functors

Source: Stacks Project, Derived Categories, Tag 015B, parts (1) and (2), specialized to
objects in degree zero (blueprint: lem-weil-pbc-derived-functor-long-exact).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory.ShortComplex.ShortExact

/-- A short exact sequence gives a full long exact sequence of right derived functors,
including the initial monomorphism. Source: Stacks Project, Tag 015B (1)-(2).
(blueprint: lem-weil-pbc-derived-functor-long-exact)

Proof:
1. Choose compatible injective resolutions of the three objects using the horseshoe
lemma (lem-weil-pbc-injective-resolution-ses, Stacks Tag 013T). Their augmentations commute
with the two maps of the short exact sequence.
2. Each degreewise short exact sequence splits, because its first term is injective
(def-sp-injective-resolutions, Stacks Tag 0136). Additivity of `F`
(def-sp-left-exact-additive) preserves the splitting identities, so applying `F` gives
another degreewise short exact sequence of complexes in the abelian target category
(def-sp-abelian).
3. Apply the long exact cohomology sequence (lem-weil-pbc-complex-ses-homology-long-exact,
Stacks Tag 0117). This gives connecting maps and exactness at every term after the first.
4. The complexes vanish in negative degrees. Their zeroth cohomology is the kernel of
the first differential; the induced map between these kernels is mono, since the
map between the degree-zero objects is a split mono. This supplies the initial zero.
5. Identify the cohomology objects and maps with the right derived functors using
lem-weil-pbc-derived-functor-map-via-lift. Conjugate each connecting map by these
comparison isomorphisms. Exactness and the initial monomorphism transport across them.
-/
theorem exists_rightDerived_full_long_exact
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [EnoughInjectives A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) :
    ∃ δ : ∀ n : ℕ, (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁,
      Mono ((F.rightDerived 0).map S.f) ∧
      ∀ n : ℕ, (S.map (F.rightDerived n)).Exact ∧
        ∃ (w₁ : (F.rightDerived n).map S.g ≫ δ n = 0)
          (w₂ : δ n ≫ (F.rightDerived (n + 1)).map S.f = 0),
          (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact := by
  obtain ⟨G, hG, _⟩ := exists_horseshoe_rightDerived_deltaFunctor F
  let P : (ℕ → A ⥤ B) → Prop := fun K ↦
    ∃ δ : ∀ n : ℕ, (K n).obj S.X₃ ⟶ (K (n + 1)).obj S.X₁,
      Mono ((K 0).map S.f) ∧
      ∀ n : ℕ, (∃ h : (K n).map S.f ≫ (K n).map S.g = 0,
          (ShortComplex.mk _ _ h).Exact) ∧
        ∃ (w₁ : (K n).map S.g ≫ δ n = 0)
          (w₂ : δ n ≫ (K (n + 1)).map S.f = 0),
          (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact
  have hP : P G.F := by
    refine ⟨G.delta S hS, G.mono_zero S hS, ?_⟩
    intro n
    refine ⟨⟨(G.exact_middle S hS n).choose, (G.exact_middle S hS n).choose_spec⟩, ?_⟩
    exact ⟨(G.exact_right S hS n).choose, (G.exact_left S hS n).choose,
      (G.exact_right S hS n).choose_spec, (G.exact_left S hS n).choose_spec⟩
  have hP' : P (fun n : ℕ ↦ F.rightDerived n) := hG ▸ hP
  rcases hP' with ⟨δ, hm, hall⟩
  refine ⟨δ, hm, ?_⟩
  intro n
  rcases hall n with ⟨hmn, hrest⟩
  rcases hrest with ⟨w1, w2, hr, hl⟩
  refine ⟨?_, w1, w2, hr, hl⟩
  simpa only [ShortComplex.map] using hmn.choose_spec

end CategoryTheory.ShortComplex.ShortExact
