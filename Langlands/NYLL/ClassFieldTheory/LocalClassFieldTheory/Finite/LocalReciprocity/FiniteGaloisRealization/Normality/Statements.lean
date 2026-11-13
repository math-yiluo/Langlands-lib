/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Realization.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U002.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Normality targets for the extension subgroups of finite Galois realizations

Adapted by Worker 4913 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, units M090.006 and M090.016 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean`.
The two source declarations are Prop-valued `Subgroup.Normal` instances. Each
is published here as a Prop-valued reducible definition whose body is exactly
the source instance type, with the source telescope as explicit binders; the
source `change`/`infer_instance` bodies and the instance registration are
deferred to a separate proof. The namespace is prefixed with `Langlands.NYLL`,
the source imports are replaced by the published modules supplying the used
declarations, and the unused `open KummerTheory`, the `noncomputable section`
and the section variables are omitted. See the paired Markdown for the
declaration map and complete modification record. The original license and
notices are retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

/-- Target of the source instance `finiteGaloisExtensionSubgroupOfEmbedding_normal`:
the fixing subgroup of an embedded finite Galois extension is normal in the absolute
subgroup. -/
abbrev finiteGaloisExtensionSubgroupOfEmbedding_normalStatement
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) : Prop :=
  (extensionSubgroup
    (closedFixingSubgroup K (SeparableClosure K)
      (⊥ : IntermediateField K (SeparableClosure K)))
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i))).Normal

/-- Target of the source instance `finiteGaloisExtensionSubgroup_normal`: the fixing
subgroup of the canonical finite Galois realization is normal. -/
abbrev finiteGaloisExtensionSubgroup_normalStatement
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] : Prop :=
  (extensionSubgroup
    (closedFixingSubgroup K (SeparableClosure K)
      (⊥ : IntermediateField K (SeparableClosure K)))
    (finiteGaloisClosedFixingSubgroup K L)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRange K L))).Normal

end Langlands.NYLL.LocalClassFieldTheory
