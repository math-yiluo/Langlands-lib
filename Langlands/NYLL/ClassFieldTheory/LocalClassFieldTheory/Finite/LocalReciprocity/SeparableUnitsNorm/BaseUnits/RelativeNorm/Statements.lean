/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Finite.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions

/-!
# Relative norms of intermediate-field units: comparison targets

Adapted by Worker 324 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M096.005 and M096.006, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`,
lines 119–171 and 173–186. Prefix the namespace with `Langlands.NYLL`,
extract only the theorem propositions as Prop-valued definitions with
`Statement` suffixes, and omit proofs. Preserve the complete source telescopes,
including finite-dimensionality and both Galois hypotheses. Reuse the
published relative norm, finiteness instance and field-unit norm through
focused imports. See the paired Markdown for all adaptations and
`licenses/NYLL/` for retained attribution.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory LocalFieldTheory ClassFormation CyclicCohomology

noncomputable section

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

section FiniteGaloisIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

/-- Proposition asserting the source relative-norm value equation on an intermediate-field unit. -/
def relativeNorm_intermediateFieldUnit_valStatement (x : Eˣ) : Prop :=
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K (x : E))

/-- Proposition asserting the source relative-norm comparison in the base fixed-unit subgroup. -/
def relativeNorm_intermediateFieldUnitStatement (x : Eˣ) : Prop :=
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E x))

end FiniteGaloisIntermediate

end
end Langlands.NYLL.LocalClassFieldTheory
