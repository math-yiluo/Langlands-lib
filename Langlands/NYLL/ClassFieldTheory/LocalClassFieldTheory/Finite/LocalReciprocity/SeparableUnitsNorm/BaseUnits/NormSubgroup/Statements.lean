/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Finite.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions

/-!
# The finite norm subgroup of separable-closure units: comparison target

Adapted by Worker 62 from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`,
lines 188–226 (M096.007; theorem type lines 190–195).

Modifications by Worker 62, 14 November 2026: extract only the proposition of
the source theorem as the Prop-valued definition
`map_finiteNormSubgroup_eq_additiveNormSubgroupStatement` and omit its proof;
prefix `LocalClassFieldTheory` with `Langlands.NYLL`; replace the source
imports by the published modules that supply `baseUnitsEquivGaloisAmbientFixed`,
the M096.003 finiteness instance, `finiteNormSubgroup` and
`additiveNormSubgroup`; drop the unused `open scoped BigOperators`; merge the
source `open` lines. The source section parameters and the proposition are
unchanged. See the paired Markdown for the complete declaration and
modification map. The original license and notices are retained in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory LocalFieldTheory ClassFormation CyclicCohomology

noncomputable section

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

section FiniteGaloisIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

/-- Proposition asserting the source M096.007 theorem: under the inverse of the
base-field fixed-unit equivalence, the abstract finite norm subgroup is exactly
the ordinary field-norm subgroup of `E` over `K`, written additively. -/
def map_finiteNormSubgroup_eq_additiveNormSubgroupStatement : Prop :=
    (finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
      additiveNormSubgroup K E

end FiniteGaloisIntermediate

end
end Langlands.NYLL.LocalClassFieldTheory
