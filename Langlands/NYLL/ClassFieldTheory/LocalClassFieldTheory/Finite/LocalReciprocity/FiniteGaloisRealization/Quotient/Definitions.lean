/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Port the definition finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
(M090.009) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FiniteGaloisRealization.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix and replace the source imports by the
published modules supplying the used declarations, including the published
instance finiteGaloisExtensionSubgroupOfEmbedding_normal (M090.006). Drop the
unused open KummerTheory. Omit all other declarations of the source file.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Realization.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Normality.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Quotient.Definitions

/-!
# The abstract quotient of an embedded finite Galois extension

For a finite Galois extension `L/K` and an embedding
`i : L →ₐ[K] SeparableClosure K`, the quotient of the base closed subgroup by
the extension subgroup of the embedded copy of `L` is identified with
`Gal(L / K)`. The group structure on the quotient uses the published normality
instance `finiteGaloisExtensionSubgroupOfEmbedding_normal`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The abstract class-formation extension quotient attached to an explicit realization
of `L/K` is the actual relative Galois group. -/
def finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ((closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K)))
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))) ≃*
      Gal(L / K) :=
  (baseFixingExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)).trans
      (AlgEquiv.autCongr
        (finiteGaloisFieldRangeEquivOfEmbedding K L i)).symm

end
end Langlands.NYLL.LocalClassFieldTheory
