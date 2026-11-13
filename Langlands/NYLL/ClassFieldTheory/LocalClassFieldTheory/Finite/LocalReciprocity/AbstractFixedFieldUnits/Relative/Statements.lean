/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Relative.Definitions

/-!
# Evaluation of the relative fixed-field unit equivalence

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory KummerTheory
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
omit [IsGalois k Ω] in
def abstractRelativeFixedFieldUnitsEquivGaloisFixed_coeStatement
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ) : Prop :=
((abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK x).1 : Additive Ωˣ) =
      intermediateFieldUnitsToGaloisAmbient k Ω
        (abstractFixedField k Ω L) x

end
end Langlands.NYLL.LocalClassFieldTheory
