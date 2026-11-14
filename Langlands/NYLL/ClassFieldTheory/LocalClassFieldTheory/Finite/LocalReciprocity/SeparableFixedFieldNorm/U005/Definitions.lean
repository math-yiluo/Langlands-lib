/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted the source definition
LocalClassFieldTheory.baseFixingCosetEquivAlgHom (inventory M165.005) as
Langlands.NYLL.LocalClassFieldTheory.baseFixingCosetEquivAlgHom. The section
variables, the type and the body are unchanged, except that the two private
source theorems baseFixingCosetToAlgHom_injective and
baseFixingCosetToAlgHom_surjective named in the body are replaced by their
published adaptations Langlands.NYLL.PortInternal.M165.d004 and
Langlands.NYLL.PortInternal.M165.d003 (inventory M165.004 and M165.003). The
namespace is prefixed with Langlands.NYLL; the NYLL imports are replaced by
the published modules proving those two theorems. All other source
declarations are omitted. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.Initial.U004.Proofs

/-!
# Cosets of the base fixing subgroup as embeddings: the equivalence

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean`,
lines 36–37 and 41 (section variables), 141–152 (inventory M165.005).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

section CosetsAndEmbeddings

variable (E : IntermediateField K Ω)

/-- Left cosets of the absolute subgroup fixing `E` are the actual
`K`-embeddings of `E` into the separably closed ambient field. -/
def baseFixingCosetEquivAlgHom
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ((closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)) ≃
      (E →ₐ[K] Ω) :=
  Equiv.ofBijective (baseFixingCosetToAlgHom K Ω E)
    ⟨Langlands.NYLL.PortInternal.M165.d004 K Ω E,
      Langlands.NYLL.PortInternal.M165.d003 K Ω E⟩

end CosetsAndEmbeddings

end
end Langlands.NYLL.LocalClassFieldTheory
