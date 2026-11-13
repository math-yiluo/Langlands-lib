/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# Base fixing subgroup and quotient surjectivity targets

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory ClassFormation
noncomputable section
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
def closedFixingSubgroup_bot_eq_baseFieldStatement : Prop :=
closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω) =
      baseField (Gal(Ω / K))

def fixingSubgroupLeBaseStatement
    (E : IntermediateField K Ω) : Prop :=
(closedFixingSubgroup K Ω E).toSubgroup ≤
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup

def baseFixingToAmbientQuotient_surjectiveStatement
    (E : IntermediateField K Ω) [IsGalois K E] : Prop :=
Function.Surjective (baseFixingToAmbientQuotient K Ω E)

end
end Langlands.NYLL.LocalClassFieldTheory
