/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 176, 10 November 2026:
Extract only M127.002 and M127.003 (lines 53–80) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuativeExtension.lean
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, omit the unused theorem Valuation.IsNontrivial.of_hasExtension
(M127.001, lines 17–51), and retain the original Mathlib-only imports, universes,
class and instance bodies. The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Valuative extensions

Records when the valuation ring of an extension field is integral over the
base valuation ring, the hypothesis needed to restrict field norms integrally.

This class is unrelated to Mathlib's root `ValuativeExtension`, which compares
valuative relations along the algebra map.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u v

open scoped ValuativeRel

/-- A valued extension whose valuation integer ring in `L` is integral over the base integer ring.

This is the algebraic input used to restrict field norms to valuation integer rings. -/
class ValuativeExtension (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] : Prop where
  /-- Every target valuation integer is integral over the base valuation
  integers. -/
  integer_isIntegral : ∀ x : 𝒪[L], IsIntegral 𝒪[K] (x : L)

/-- An integral-closure identification of valuation rings makes the target valuation an extension of
the base valuation. -/
instance valuativeExtensionOfIsIntegralClosure
    (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    ValuativeExtension K L where
  integer_isIntegral x :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2 ⟨x, rfl⟩

end
end Langlands.NYLL.LocalFieldTheory
