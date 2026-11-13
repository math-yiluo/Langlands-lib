/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U002.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Base-fixing extension subgroup and quotient-kernel targets

Adapted by Worker 4913 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, units M089.003 and M089.007 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`.
The two source theorems become Prop-valued definitions with the suffix
`Statement`; their proofs are omitted. The namespace is prefixed with
`Langlands.NYLL`, the source imports are replaced by the published modules
supplying the used declarations, and the unused `open ClassFormation` is
omitted. The M089.007 docstring names the map, since the preceding source
definition is not in this file. See the paired Markdown for the declaration
map and complete modification record. The original license and notices are
retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- In the base fixing group, the abstract class-formation extension subgroup is exactly
the subgroup obtained from the ambient fixing subgroup by `subgroupOf`. -/
def extensionSubgroup_base_eq_subgroupOfStatement
    (E : IntermediateField K Ω) : Prop :=
  extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E) =
    (closedFixingSubgroup K Ω E).toSubgroup.subgroupOf
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup

/-- The kernel of the base-to-ambient quotient map is the exact `extensionSubgroup` used in
the abstract theory. -/
def baseFixingToAmbientQuotient_kerStatement
    (E : IntermediateField K Ω) [IsGalois K E] : Prop :=
  (baseFixingToAmbientQuotient K Ω E).ker =
    extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)

end
end Langlands.NYLL.LocalClassFieldTheory
