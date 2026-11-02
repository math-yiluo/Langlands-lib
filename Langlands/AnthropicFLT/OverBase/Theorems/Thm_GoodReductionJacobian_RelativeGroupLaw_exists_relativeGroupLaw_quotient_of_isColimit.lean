/-
Adapted from `Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.OverBase.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GroupLawOverBase

universe u

theorem GroupLawOverBase.RelativeGroupLaw.exists_relativeGroupLaw_quotient_of_isColimit
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
      (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
    (hcoeq : IsColimit (Cofork.ofπ p w)) :
    ∃ (g : P ⟶ S) (hg : p ≫ g = f) (LP : RelativeGroupLaw S g),
      (∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t f),
        (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t g),
        LP.mul t x y = LP.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t f),
        (⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ : SchemeHomOver t g) = LP.one t ↔
          ∃ e : T ⟶ E, e ≫ ι = x.1) :=
  P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit_overBase.solution L ι hE_one hE_mul hE_inv hcomm p w hR hcoeq
