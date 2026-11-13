/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract the private theorem M267.008
from commit fbd320cd8b1b06487c58227e92eb135794267709 as the closed
Prop-valued target Langlands.NYLL.PortInternal.M267.d008Statement,
following the published port inventory. Preserve the source Type universes,
section telescope and conclusion; import only the published norm quotient
and unramifiedness class, together with Mathlib cardinal and Galois support.
The source proof remains a separate obligation. License and notices are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U002.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.Definitions
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality of the actual unramified norm quotient: proposition target

Source: private theorem M267.008 in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`.
-/

namespace Langlands.NYLL.PortInternal.M267

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The actual unramified norm quotient has cardinality equal to the degree. -/
def d008Statement : Prop :=
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
    [IsUnramifiedValuedExtension K L],
    Nat.card (NormQuotient K L) = Module.finrank K L

end Langlands.NYLL.PortInternal.M267
