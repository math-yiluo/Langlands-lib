/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Quotient.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions

/-!
# Base-unit value and intermediate-field coset-action targets

Adapted by Worker 324 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M096.002 and M096.004, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`,
lines 52–58 and 75–117. Prefix the namespace with `Langlands.NYLL`, extract
only the theorem propositions as Prop-valued definitions with `Statement`
suffixes, and omit proofs and the source `simp` attribute. Preserve the
source telescopes, including the finite-dimensional omission for M096.004.
Use focused Library imports and documentation; see the paired Markdown for
all adaptations and `licenses/NYLL/` for retained attribution.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory

noncomputable section

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

/-- Proposition asserting the source value equation for the base-unit equivalence. -/
def baseUnitsEquivGaloisAmbientFixed_valStatement (x : Kˣ) : Prop :=
    ((Additive.toMul
      ((baseUnitsEquivGaloisAmbientFixed K Ω (Additive.ofMul x)).1 :
        Additive Ωˣ) : Ωˣ) : Ω) = algebraMap K Ω (x : K)

section FiniteGaloisIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]

open ClassFormation CyclicCohomology

omit [FiniteDimensional K E] in
/-- Proposition asserting the source coset-action value equation on an intermediate-field unit. -/
def relativeCosetAction_intermediateFieldUnit_valStatement
    (x : Eˣ)
    (q : (closedFixingSubgroup K Ω
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E)
        (fixingSubgroupLeBase K Ω E)) : Prop :=
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E q) (x : E))

end FiniteGaloisIntermediate

end
end Langlands.NYLL.LocalClassFieldTheory
