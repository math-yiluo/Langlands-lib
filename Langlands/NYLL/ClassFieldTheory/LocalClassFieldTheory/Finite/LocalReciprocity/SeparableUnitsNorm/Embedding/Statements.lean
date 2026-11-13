/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Norm invariance under embedded field realization

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open LocalFieldTheory
noncomputable section
variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]
section EmbeddedFiniteGaloisExtension
variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] Ω)
omit [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L] in
def normUnits_embeddedExtensionAlgEquivStatement (x : Lˣ) : Prop :=
normUnits K (AlgHom.fieldRange i)
        (Units.mapEquiv (AlgEquiv.ofInjectiveField i).toMulEquiv x) =
      normUnits K L x

omit [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L] in
def localNormSubgroup_fieldRange_eqStatement : Prop :=
localNormSubgroup K (AlgHom.fieldRange i) = localNormSubgroup K L

end EmbeddedFiniteGaloisExtension
end
end Langlands.NYLL.LocalClassFieldTheory
