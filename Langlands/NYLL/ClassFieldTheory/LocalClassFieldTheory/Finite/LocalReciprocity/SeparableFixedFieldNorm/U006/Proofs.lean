/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 368, 15 November 2026: adapt the source instance
LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable
(inventory M165.006, lines 154–162 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709) to prove the
published target
Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparableStatement;
prefix the namespace with Langlands.NYLL; write the section variables as
explicit binders; declare it as a theorem and register it with
`attribute [instance]`; replace the source imports by the published target
and the published definition of baseFixingCosetEquivAlgHom. The proof term is
the source's. The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U006.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm.U005.Definitions

/-!
# Cosets of the base fixing subgroup: finiteness

The proof of the NYLL M165.006 instance for the exact published target,
registered as a global instance as in the source.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology

/-- Provides the instance `baseFixingExtensionQuotient_finite_of_isSeparable`. -/
theorem baseFixingExtensionQuotient_finite_of_isSeparable
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (E : IntermediateField K Ω)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    baseFixingExtensionQuotient_finite_of_isSeparableStatement K Ω E :=
  (baseFixingCosetEquivAlgHom K Ω E).finite_iff.mpr inferInstance

attribute [instance] baseFixingExtensionQuotient_finite_of_isSeparable

end Langlands.NYLL.LocalClassFieldTheory
