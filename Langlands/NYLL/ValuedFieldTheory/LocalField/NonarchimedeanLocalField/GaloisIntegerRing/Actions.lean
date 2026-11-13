/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 202, 13 November 2026: extract the listed data from
upstream fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, and reduce imports. See the paired Markdown for the exact
correspondence and modification record. LICENSE and NOTICE are retained
under licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs
import Mathlib.Algebra.Ring.Action.Basic

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Real Galois automorphisms act on `𝒪[L]` through the actual integral-closure
restriction. -/
def galoisGroupIntegerRingEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝒪[L] ≃+* 𝒪[L]) where
  toFun := galoisGroupIntegerRingEquivOfIsIntegralClosure K L
  map_one' := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L 1 x : 𝒪[L]) : L) =
      (x : L)
    rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
    rfl
  map_mul' := by
    intro σ τ
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    change ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L (σ * τ) x : 𝒪[L]) : L) =
      ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L τ x) : 𝒪[L]) : L)
    rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply,
      galoisGroupIntegerRingEquivOfIsIntegralClosure_apply,
      galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]
    rfl

/-- The semiring action on the valuation integer ring induced by the actual
integral-closure restriction of `Gal(L / K)`. -/
@[reducible]
def galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulSemiringAction (Gal(L / K)) 𝒪[L] :=
  MulSemiringAction.compHom 𝒪[L] (galoisGroupIntegerRingEquivHomOfIsIntegralClosure K L)


end

end Langlands.NYLL.LocalFieldTheory
