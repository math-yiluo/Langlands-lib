/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Quotient.Definitions

/-!
# Finiteness of the abstract quotient of a finite Galois intermediate extension

Adapted by Worker 57 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, unit M096.003 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`.
The namespace is prefixed with `Langlands.NYLL` and the source imports are
replaced by the published module supplying the used declarations. See the
paired Markdown for the declaration map and complete modification record. The
original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

noncomputable section

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

section FiniteGaloisIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

/-- Provides the instance `baseFixingExtensionQuotient_finite`. -/
noncomputable instance baseFixingExtensionQuotient_finite :
    Finite ((closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E)
        (fixingSubgroupLeBase K Ω E)) :=
  (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).toEquiv.finite_iff.mpr
    inferInstance

end FiniteGaloisIntermediate

end
end Langlands.NYLL.LocalClassFieldTheory
