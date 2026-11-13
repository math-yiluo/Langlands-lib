/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M088.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published FixedUnits Statements module.
State the theorem as the published Statement applied to the source
parameters and keep the original proof term rfl. Omit the simp attribute,
which does not apply to a theorem whose type is a Prop-valued definition.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.Statements

/-!
# Evaluation of the intermediate-field unit inclusion

The exact proof that the additive inclusion `Additive Eˣ →+ Additive Ωˣ` sends
`Additive.ofMul x` to `Additive.ofMul` of the image of `x` under the unit map of
the inclusion `E → Ω`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

/-- States the theorem `intermediateFieldUnitsToGaloisAmbient_apply`. -/
theorem intermediateFieldUnitsToGaloisAmbient_apply
    (E : IntermediateField K Ω) (x : Eˣ) :
    intermediateFieldUnitsToGaloisAmbient_applyStatement K Ω E x :=
  rfl

end Langlands.NYLL.LocalClassFieldTheory
