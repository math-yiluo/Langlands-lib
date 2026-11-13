/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only M277.004 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldNormResidueNaturality.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and keep the source section variables, docstring and body. Replace
the source imports by the published modules defining the relative fixed
field and the unit norm, and open only the namespace of normUnits. Omit all
other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions

/-!
# The unit norm between two concrete fixed fields

The ordinary field norm, on unit groups written additively, from an upper
concrete fixed field to a lower one inside a common Galois ambient field.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The ordinary field norm on units between two concrete fixed fields. -/
def abstractFixedFieldNormUnits
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    Additive (abstractRelativeFixedField k Ω hK'K)ˣ →+
      Additive (abstractFixedField k Ω K)ˣ :=
  MonoidHom.toAdditive
    (normUnits (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hK'K))

end Langlands.NYLL.LocalClassFieldTheory

end
