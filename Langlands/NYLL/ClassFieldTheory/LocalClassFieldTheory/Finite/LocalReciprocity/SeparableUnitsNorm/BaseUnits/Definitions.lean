/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions

/-!
# Base-field units as Galois-fixed ambient units

Adapted by Worker 324 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M096.001, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean`,
lines 39–50. Extract the definition and preserve its full body and telescope;
prefix the namespace with `Langlands.NYLL` and replace the broad source imports
by the focused intermediate-field equivalence module. Remove unused openings
and replace whole-file documentation. See the paired Markdown for the full
modification and source record and `licenses/NYLL/` for retained attribution.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory

noncomputable section

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

/-- Canonical identification of `Kˣ` with the coefficient group fixed by the
full absolute Galois group. -/
def baseUnitsEquivGaloisAmbientFixed :
    Additive Kˣ ≃+ ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)) := by
  let eBot : Additive Kˣ ≃+
      Additive (⊥ : IntermediateField K Ω)ˣ :=
    MulEquiv.toAdditive
      (Units.mapEquiv (IntermediateField.botEquiv K Ω).symm.toMulEquiv)
  exact eBot.trans
    (intermediateFieldUnitsEquivGaloisFixed K Ω ⊥)

end
end Langlands.NYLL.LocalClassFieldTheory
