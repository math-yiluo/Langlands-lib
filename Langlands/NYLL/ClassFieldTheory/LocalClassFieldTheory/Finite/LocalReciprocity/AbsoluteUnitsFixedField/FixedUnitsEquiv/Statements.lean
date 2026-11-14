/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions

/-!
# Coercion target for the intermediate-field fixed-unit equivalence

Adapted by Worker 324 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M088.007, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean`,
lines 164–170. Extract only the proposition, prefix the namespace with
`Langlands.NYLL`, append `Statement`, replace `theorem` by `def ... : Prop :=`,
and remove the theorem proof and its `simp` attribute. Import the focused
equivalence definition. See the paired Markdown and `licenses/NYLL/`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Proposition asserting the source coercion equation for the fixed-unit equivalence. -/
def intermediateFieldUnitsEquivGaloisFixed_coeStatement
    (E : IntermediateField K Ω) (x : Additive Eˣ) : Prop :=
    (intermediateFieldUnitsEquivGaloisFixed K Ω E x).1 =
        intermediateFieldUnitsToGaloisAmbient K Ω E x

end
end Langlands.NYLL.LocalClassFieldTheory
