/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 120, 14 November 2026: extract the proof of M140.007 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean,
lines 101-116, at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix
the namespace with Langlands.NYLL, import the published IntegerStatements
module and the published GaloisIntegerRing proof module, and prove the
published target applied to all its parameters, after unfolding it, with the
original proof except its final rfl: the published integer-ring restriction
is built from Mathlib's galRestrict', so after the original ext the goal is
changed to the ambient value of that restriction and closed by the published
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_apply (M139.003). Omit the source noncomputable section and all
other source declarations. See the paired Markdown; the original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs

/-!
# Equivariance of the inclusion of integer units

The inclusion `𝒪[L]ˣ → Lˣ` commutes with the integral-closure Galois action
on integer units and the canonical Galois action on field units.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The inclusion `𝒪_Lˣ → Lˣ` is equivariant for the actual actions. -/
theorem integerUnitsToFieldUnits_galoisGroup_equivariant
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]ˣ) :
    integerUnitsToFieldUnits_galoisGroup_equivariantStatement K L σ x := by
  unfold integerUnitsToFieldUnits_galoisGroup_equivariantStatement
  intro hIntegerAction hFieldAction
  ext
  -- Both sides unfold to ambient-field values; the published restriction is
  -- built from `galRestrict'`, so its value is supplied by M139.003.
  change
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (x : 𝒪[L]) : 𝒪[L]) : L) =
      σ ((x : 𝒪[L]) : L)
  exact galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L σ (x : 𝒪[L])

end Langlands.NYLL.LocalClassFieldTheory
