/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Realization.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Finite.Definitions

/-!
# The finite abstract extension object of an embedded finite Galois extension

Adapted by Worker 57 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M097.005 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityTransport.lean`.
The namespace is prefixed with `Langlands.NYLL`, the source imports are
replaced by the published modules supplying the used declarations, and the
source's private abbreviation `B` is replaced by its published port
`Langlands.NYLL.PortInternal.M097.d003`. The `normal` field, which the source
fills by instance search through the instance
`finiteGaloisExtensionSubgroupOfEmbedding_normal` (not published in the
Library), is filled by that instance's source proof, written inline. See the
paired Markdown for the declaration map and complete modification record. The original license and
notices are retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology ClassFormation

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The finite abstract extension object determined by an explicit
embedding of `L` into the fixed separable closure. -/
def finiteGaloisAbstractExtensionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteGaloisSubextension (PortInternal.M097.d003 K) where
  field := finiteGaloisClosedFixingSubgroupOfEmbedding K L i
  below := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  normal := by
    change
      (extensionSubgroup
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K)))
        (closedFixingSubgroup K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))).Normal
    infer_instance
  finite := baseFixingExtensionQuotient_finite K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

end
end Langlands.NYLL.LocalClassFieldTheory
