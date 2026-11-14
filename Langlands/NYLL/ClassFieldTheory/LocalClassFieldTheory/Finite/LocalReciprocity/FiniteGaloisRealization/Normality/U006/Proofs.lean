/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Normality.Statements

/-!
# Normality of the extension subgroup of an embedded finite Galois extension

Adapted by Worker 447 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M090.006 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean`.
The source instance is ported as a theorem whose type is the published target
`finiteGaloisExtensionSubgroupOfEmbedding_normalStatement`, followed by
`attribute [instance]`, which registers it as an instance under the source name.
The source `change`/`infer_instance` proof is retained. The paired Markdown records
the extraction and modifications.
Original license and notices: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology

/-- The fixing subgroup of an embedded finite Galois extension is normal in the absolute
subgroup. -/
theorem finiteGaloisExtensionSubgroupOfEmbedding_normal
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    finiteGaloisExtensionSubgroupOfEmbedding_normalStatement K L i := by
  change
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (closedFixingSubgroup K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).Normal
  infer_instance

attribute [instance] finiteGaloisExtensionSubgroupOfEmbedding_normal

end Langlands.NYLL.LocalClassFieldTheory
