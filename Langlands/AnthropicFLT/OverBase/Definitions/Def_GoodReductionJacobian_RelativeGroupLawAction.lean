/-
Adapted from `Definitions/Def_GoodReductionJacobian_RelativeGroupLawAction.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: generalized from the base `Spec R` of a commutative ring `R` to an arbitrary base
scheme `S`, with the namespace `GoodReductionJacobian` renamed `GroupLawOverBase`; FLT
commands from `P2M.Util` are replaced by standard Lean commands. The paired Markdown file
lists all changes.
-/
import Mathlib
import Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GroupLawOverBase.RelativeGroupLaw

variable {S : Scheme.{u}} {J : Scheme.{u}} {f : J ⟶ S}

abbrev actionSource (f : J ⟶ S) {E : Scheme.{u}} (ι : E ⟶ J) :
    pullback (ι ≫ f) f ⟶ S :=
  pullback.snd (ι ≫ f) f ≫ f

def actionFstPoint (L : RelativeGroupLaw S f) {E : Scheme.{u}} (ι : E ⟶ J) :
    SchemeHomOver (actionSource f ι) f :=
  ⟨pullback.fst (ι ≫ f) f ≫ ι, by rw [Category.assoc, pullback.condition]⟩

def actionSndPoint (L : RelativeGroupLaw S f) {E : Scheme.{u}} (ι : E ⟶ J) :
    SchemeHomOver (actionSource f ι) f :=
  ⟨pullback.snd (ι ≫ f) f, rfl⟩

def action (L : RelativeGroupLaw S f) {E : Scheme.{u}} (ι : E ⟶ J) : pullback (ι ≫ f) f ⟶ J :=
  (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).1

theorem action_def (L : RelativeGroupLaw S f) {E : Scheme.{u}} (ι : E ⟶ J) :
    L.action ι = (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).1 := rfl

@[simp] theorem actionFstPoint_coe (L : RelativeGroupLaw S f) {E : Scheme.{u}} (ι : E ⟶ J) :
    (L.actionFstPoint ι).1 = pullback.fst (ι ≫ f) f ≫ ι := rfl

@[simp] theorem actionSndPoint_coe (L : RelativeGroupLaw S f) {E : Scheme.{u}} (ι : E ⟶ J) :
    (L.actionSndPoint ι).1 = pullback.snd (ι ≫ f) f := rfl

theorem action_over (L : RelativeGroupLaw S f) {E : Scheme.{u}} (ι : E ⟶ J) :
    L.action ι ≫ f = actionSource f ι :=
  (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).2

end GroupLawOverBase.RelativeGroupLaw

end
