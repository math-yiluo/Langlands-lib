/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 205, 2026-11-16: extract M267.002, source lines 61–72,
from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace
with Langlands.NYLL and replace the source imports by the published
M267.001 proof, M266.017 proof and M093.007 definition. Keep the source
Type-0 section telescope, docstring and definition body unchanged; omit
unrelated declarations and the redundant noncomputable section.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U001.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U017.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U007.Definitions

/-!
# The canonical map from the norm quotient to the valuation quotient

NYLL source unit M267.002, with the published norm-subgroup inclusion.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type)
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

/-- The canonical map from the norm quotient to the valuation quotient. -/
noncomputable def normQuotientToUnramifiedNormQuotient :
    NormQuotient K L →*
      Kˣ ⧸ unramifiedNormSubgroup K (Module.finrank K L) :=
  normQuotientLift
    (unramifiedNormClass K (Module.finrank K L))
    (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (unramifiedNormClass_eq_one_iff_mem K (Module.finrank K L) x).2
        (localNormSubgroup_le_unramifiedNormSubgroup K L hx))

end Langlands.NYLL.LocalClassFieldTheory
