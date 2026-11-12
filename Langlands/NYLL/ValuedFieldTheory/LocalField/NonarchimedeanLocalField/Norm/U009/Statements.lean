/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 176, 12 November 2026:
Extract only the statement of M129.009 (lines 101–107, with its section
context at lines 20–30 and 63–65) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued definition.
Prefix the namespace with Langlands.NYLL, keep the universes u and v and the
complete source telescope in its original order, and replace the source
imports by the published ValuativeExtension.Definitions module and Mathlib's
RingTheory.Norm.Defs. The proof and all other declarations are omitted.
See paired Markdown. The upstream LICENSE and NOTICE are preserved in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension.Definitions
import Mathlib.RingTheory.Norm.Defs

/-!
# Norms of valuation integers

The closed proposition that the field norm of a valuation-ring element of an
extension lies in the base valuation ring, under the published integrality
class.
-/

namespace Langlands.NYLL.LocalFieldTheory

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

/-- The norm of an element integral over the base valuation ring lies in the base valuation ring.
This is the closed statement target for NYLL M129.009. -/
def algebraNorm_mem_integers_of_mem_integersStatement.{u, v} : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]),
    Algebra.norm K (x : L) ∈ 𝒪[K]

end IsNonarchimedeanLocalField

end Langlands.NYLL.LocalFieldTheory
