/-
Adapted from `Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: generalized from the base `Spec R` of a commutative ring `R` to an arbitrary base
scheme `S`, with the namespace `GoodReductionJacobian` renamed `GroupLawOverBase`; FLT
commands from `P2M.Util` are replaced by standard Lean commands. The paired Markdown file
lists all changes.
-/
import Mathlib
import Langlands.AnthropicFLT.OverBase.Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Langlands.AnthropicFLT.OverBase.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GroupLawOverBase

universe u

theorem GroupLawOverBase.RelativeGroupLaw.finiteLocallyFree_mono_equivalence_actionGroupoid
    {S : Scheme.{u}}
    {J : Scheme.{u}} {f : J ⟶ S} (L : RelativeGroupLaw S f)
    {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
    [IsFinite (ι ≫ f)] [Flat (ι ≫ f)] [LocallyOfFinitePresentation (ι ≫ f)]
    (hE_one : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      ∃ e : T ⟶ E, e ≫ ι = (L.one t).1)
    (hE_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) →
        ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1)
    (hE_inv : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t f),
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1) :
    IsFinite (pullback.snd (ι ≫ f) f) ∧ Flat (pullback.snd (ι ≫ f) f) ∧
      LocallyOfFinitePresentation (pullback.snd (ι ≫ f) f) ∧
    IsFinite (L.action ι) ∧ Flat (L.action ι) ∧ LocallyOfFinitePresentation (L.action ι) ∧
    (∀ {T : Scheme.{u}} (a b : T ⟶ pullback (ι ≫ f) f),
      a ≫ pullback.snd (ι ≫ f) f = b ≫ pullback.snd (ι ≫ f) f → a ≫ L.action ι = b ≫ L.action ι → a = b) ∧
    (∀ T : Scheme.{u}, _root_.Equivalence fun x y : T ⟶ J =>
      ∃ φ : T ⟶ pullback (ι ≫ f) f, φ ≫ pullback.snd (ι ≫ f) f = x ∧ φ ≫ L.action ι = y) :=
  P2MW.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_mono_equivalence_actionGroupoid_overBase.solution L ι hE_one hE_mul hE_inv
