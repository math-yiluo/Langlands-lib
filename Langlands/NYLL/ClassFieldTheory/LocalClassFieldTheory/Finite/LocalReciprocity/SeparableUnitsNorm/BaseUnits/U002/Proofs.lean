/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 15 November 2026 UTC:
Extract only the proof of M096.002 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the published SeparableUnitsNorm.BaseUnits
Statements module, keep the source section variables, drop the source simp
attribute and the unused openings and noncomputable section, and state the
theorem as the published Statement applied to the source parameters. The
proof `by rfl` is unchanged. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Statements

/-!
# Value of the base-unit fixed-coefficient equivalence

The proof that the ambient value of `baseUnitsEquivGaloisAmbientFixed` at
`x : Kˣ` is `algebraMap K Ω x`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

/-- The ambient value of the base-unit equivalence is the image of the unit
under `algebraMap K Ω`. -/
theorem baseUnitsEquivGaloisAmbientFixed_val (x : Kˣ) :
    baseUnitsEquivGaloisAmbientFixed_valStatement K Ω x := by
  rfl

end Langlands.NYLL.LocalClassFieldTheory
