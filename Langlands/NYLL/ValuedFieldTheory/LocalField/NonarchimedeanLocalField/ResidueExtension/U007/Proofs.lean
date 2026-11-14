/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M138.007 (residueField_algebraMap_residue) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published ResidueExtension
ResidueStatement module. Keep the noncomputable section, `universe u`,
`open scoped ValuativeRel`, the docstring and the `@[simp]` attribute, and
state the theorem as the published Statement applied to the source
parameters. The proof is unchanged. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.ResidueStatement

/-!
# Residue compatibility of a valuation extension

The proof that the residue-field algebra map commutes with reduction of
valuation-ring elements.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The residue-field algebra map commutes with reduction of valuation-ring elements. -/
@[simp]
theorem residueField_algebraMap_residue (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝒪[K]) :
    residueField_algebraMap_residueStatement K L x :=
  rfl

end

end Langlands.NYLL.LocalFieldTheory
