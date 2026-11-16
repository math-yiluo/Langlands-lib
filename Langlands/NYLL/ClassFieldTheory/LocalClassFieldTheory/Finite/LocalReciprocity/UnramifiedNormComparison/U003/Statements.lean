/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 205, 2026-11-16: extract M267.003, source lines 73–79,
from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace
with Langlands.NYLL and close the unchanged Type-0 telescope and conclusion
into a Prop-valued definition with suffix Statement. Import only the adapted
M267.002 data module; omit the source proof and its proof attributes.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U002.Definitions

/-! # NYLL M267.003: canonical comparison proposition target -/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The comparison map sends a norm class to the corresponding unramified valuation class. -/
def normQuotientToUnramifiedNormQuotient_mkStatement : Prop :=
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
    (x : Kˣ),
    normQuotientToUnramifiedNormQuotient K L
        (normClass K L x) =
      unramifiedNormClass K (Module.finrank K L) x

end Langlands.NYLL.LocalClassFieldTheory
