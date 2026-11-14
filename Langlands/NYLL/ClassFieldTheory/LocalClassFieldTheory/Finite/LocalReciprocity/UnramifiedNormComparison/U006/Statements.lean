/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-14: extract M267.006, lines 103–109 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace
with Langlands.NYLL and close the original Type-0 telescope into a Prop-valued
definition. Import the focused adapted M267.005 definition. The original
proof and simp attribute remain a separate proof unit.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U005.Definitions

/-! # The canonical projection formula: proposition target -/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The cyclic Galois-group equivalence is the canonical map to the abelianization. -/
def galoisGroupEquivAbelianizationOfUnramifiedValuation_applyStatement : Prop :=
  ∀ (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
    (σ : Gal(L / K)),
    galoisGroupEquivAbelianizationOfUnramifiedValuation K L σ =
      Abelianization.of σ

end Langlands.NYLL.LocalClassFieldTheory
