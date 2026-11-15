/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 15 November 2026 UTC:
Extract only the proof of M088.007 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the published AbsoluteUnitsFixedField
FixedUnitsEquiv Statements module, keep the source section variables, drop
the source simp attribute and the unused openings and noncomputable section,
and state the theorem as the published Statement applied to the source
parameters. The proof `rfl` is unchanged. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Statements

/-!
# Coercion law for the intermediate-field fixed-unit equivalence

The proof that the ambient value of `intermediateFieldUnitsEquivGaloisFixed`
at `x : Additive Eˣ` is the image of `x` under
`intermediateFieldUnitsToGaloisAmbient`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The underlying ambient unit of the fixed-unit equivalence is the image of
the intermediate-field unit. -/
theorem intermediateFieldUnitsEquivGaloisFixed_coe
    (E : IntermediateField K Ω) (x : Additive Eˣ) :
    intermediateFieldUnitsEquivGaloisFixed_coeStatement K Ω E x :=
  rfl

end Langlands.NYLL.LocalClassFieldTheory
