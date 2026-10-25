/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 463 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
the two theorem signatures are packaged as universally quantified Prop targets
in Langlands.NYLL, with explicit independent universes and a focused Mathlib
import. The proofs are omitted. See licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.RingTheory.Valuation.Extension

/-!
# Generic valuation-extension transport: statements

These two targets retain the field/group scope of transport along compatible
ring equivalences and the ring/monoid scope of replacement by equivalent
valuations. They use Mathlib's `Valuation.HasExtension` and `Valuation.IsEquiv`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe uF uG uF₀ uG₀ uΓF uΓG uΓF' uΓG'

/-- Pulling valuations back along a commuting square of field equivalences
preserves the valuation-extension relation. -/
def hasExtension_comap_ringEquivsStatement : Prop :=
  ∀ {F : Type uF} {G : Type uG} {F₀ : Type uF₀} {G₀ : Type uG₀}
    [Field F] [Field G] [Field F₀] [Field G₀]
    [Algebra F G] [Algebra F₀ G₀]
    {ΓF : Type uΓF} {ΓG : Type uΓG}
    [LinearOrderedCommGroupWithZero ΓF]
    [LinearOrderedCommGroupWithZero ΓG]
    (eF : F₀ ≃+* F) (eG : G₀ ≃+* G),
    (∀ a : F₀, eG (algebraMap F₀ G₀ a) = algebraMap F G (eF a)) →
    ∀ (vF : Valuation F ΓF) (vG : Valuation G ΓG) [vF.HasExtension vG],
      (vF.comap eF.toRingHom).HasExtension (vG.comap eG.toRingHom)

/-- Replacing both valuations by equivalent valuations preserves the
valuation-extension relation over a commutative base ring and a ring algebra. -/
def hasExtension_of_isEquivStatement : Prop :=
  ∀ {F : Type uF} {G : Type uG}
    [CommRing F] [Ring G] [Algebra F G]
    {ΓF : Type uΓF} {ΓF' : Type uΓF'} {ΓG : Type uΓG} {ΓG' : Type uΓG'}
    [LinearOrderedCommMonoidWithZero ΓF]
    [LinearOrderedCommMonoidWithZero ΓF']
    [LinearOrderedCommMonoidWithZero ΓG]
    [LinearOrderedCommMonoidWithZero ΓG']
    (vF : Valuation F ΓF) (vF' : Valuation F ΓF')
    (vG : Valuation G ΓG) (vG' : Valuation G ΓG') [vF.HasExtension vG],
      vF.IsEquiv vF' → vG.IsEquiv vG' → vF'.HasExtension vG'

end Langlands.NYLL.LocalFieldTheory
