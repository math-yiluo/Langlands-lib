/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.U005.Proofs

/-!
# Intermediate-field units as fixed ambient units

Adapted by Worker 324 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`, M088.006, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean`,
lines 148–162. Extract the definition with its unchanged body and proof terms,
prefix the namespace with `Langlands.NYLL`, and replace broad source imports by
the published range-proof module. See the paired Markdown for the full source
map and modification record. Original attribution is retained above and in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Canonical additive equivalence `Eˣ ≃ A_E` for the actual ambient-unit
representation. -/
def intermediateFieldUnitsEquivGaloisFixed
    (E : IntermediateField K Ω) :
    Additive Eˣ ≃+ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω E) := by
  let eRange : Additive Eˣ ≃+
      (intermediateFieldUnitsToGaloisAmbient K Ω E).range :=
    AddMonoidHom.ofInjective (by
      intro x y hxy
      apply Additive.toMul.injective
      exact (Units.map_injective E.val.injective) (congrArg Additive.toMul hxy))
  exact eRange.trans
    (AddEquiv.addSubgroupCongr
      (intermediateFieldUnitsToGaloisAmbient_range K Ω E))

end
end Langlands.NYLL.LocalClassFieldTheory
