/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M088.005 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FixedUnits Statements module and the
published M088.003 and M088.004 proof modules, and open only
RamificationTheory and KummerTheory. State the theorem as the published
Statement applied to the source parameters. The proof is unchanged. The
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.U004.Proofs

/-!
# Range of the intermediate-field unit inclusion

The proof that the image of `Eˣ` in `Ωˣ` is the subgroup of ambient units fixed
by the closed fixing subgroup of `E`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The image of `Eˣ` in `Ωˣ` is precisely the abstract fixed
subgroup `A_E` used in the abstract class-formation framework. -/
theorem intermediateFieldUnitsToGaloisAmbient_range
    (E : IntermediateField K Ω) :
    intermediateFieldUnitsToGaloisAmbient_rangeStatement K Ω E := by
  apply AddSubgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    change
      (show galoisAmbientUnitsRep K Ω from
        intermediateFieldUnitsToGaloisAmbient K Ω E y) ∈
        ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω E)
    apply (mem_galoisAmbientUnits_fixed_iff K Ω E _).2
    rw [← ofMul_toMul y, intermediateFieldUnitsToGaloisAmbient_apply,
      toMul_ofMul, Units.coe_map]
    exact (Additive.toMul y : Eˣ).1.property
  · intro hx
    have hxE :
        ((Additive.toMul x : Ωˣ) : Ω) ∈ E :=
      (mem_galoisAmbientUnits_fixed_iff K Ω E x).1 hx
    let y₀ : E :=
      ⟨((Additive.toMul x : Ωˣ) : Ω), hxE⟩
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have h' :
          ((Additive.toMul x : Ωˣ) : Ω) = 0 :=
        congrArg E.val h
      exact (Additive.toMul x : Ωˣ).ne_zero h'
    let y : Eˣ := Units.mk0 y₀ hy₀
    refine ⟨Additive.ofMul y, ?_⟩
    rw [intermediateFieldUnitsToGaloisAmbient_apply]
    apply Additive.ext
    rw [toMul_ofMul]
    apply Units.ext
    rw [Units.coe_map]
    rfl

end Langlands.NYLL.LocalClassFieldTheory
