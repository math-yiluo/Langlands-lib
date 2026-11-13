/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Normal fixing subgroup and base-to-ambient quotient map

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory
noncomputable section
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
/-- The fixing subgroup of a Galois intermediate extension is normal in the
ambient Galois group. -/
instance closedFixingSubgroup_normal
    (E : IntermediateField K Ω) [IsGalois K E] :
    (closedFixingSubgroup K Ω E).toSubgroup.Normal :=
  (InfiniteGalois.normal_iff_isGalois E).2 inferInstance

/-- The quotient map from the abstract class-formation base fixing group to the ordinary
ambient quotient by `Gal(Ω/E)`. -/
def baseFixingToAmbientQuotient
    (E : IntermediateField K Ω) [IsGalois K E] :
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup →*
      Gal(Ω / K) ⧸ (closedFixingSubgroup K Ω E).toSubgroup :=
  (QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup).comp
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup.subtype
end
end Langlands.NYLL.LocalClassFieldTheory
