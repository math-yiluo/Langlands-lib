/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.Initial.Definitions
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions

/-!
# Fixed-field units and Galois-fixed ambient coefficients

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
/-- Units of the concrete fixed field represented by an arbitrary closed
subgroup, identified directly with the corresponding fixed coefficients. -/
def abstractFixedFieldUnitsEquivGaloisFixed
    (H : ClosedSubgroup (Gal(Ω/k))) :
    Additive (abstractFixedField k Ω H)ˣ ≃+
      ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) H where
  toFun x := ⟨intermediateFieldUnitsToGaloisAmbient k Ω
      (abstractFixedField k Ω H) x, by
    intro σ
    apply Additive.ext
    apply Units.ext
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup
      ((Additive.toMul x : (abstractFixedField k Ω H)ˣ) : Ω)).1
        (Additive.toMul x : (abstractFixedField k Ω H)ˣ).1.property σ.1 σ.2⟩
  invFun a := by
    have ha : ((Additive.toMul a.1 : Ωˣ) : Ω) ∈
        abstractFixedField k Ω H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hfixed := a.2 ⟨σ, hσ⟩
      exact congrArg
        (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) hfixed
    let y₀ : abstractFixedField k Ω H :=
      ⟨((Additive.toMul a.1 : Ωˣ) : Ω), ha⟩
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have h' : ((Additive.toMul a.1 : Ωˣ) : Ω) = 0 :=
        congrArg (abstractFixedField k Ω H).val h
      exact (Additive.toMul a.1 : Ωˣ).ne_zero h'
    exact Additive.ofMul (Units.mk0 y₀ hy₀)
  left_inv x := by
    apply Additive.ext
    apply Units.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl
end
end Langlands.NYLL.LocalClassFieldTheory
