/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Frobenius.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.U011.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.U009.Proofs

/-!
# Finite local reciprocity: the fixed field of the Frobenius image (proof)

Modified by Worker 46: prove the published target
`Langlands.NYLL.LocalClassFieldTheory.fixedField_residueAbsoluteFrobeniusRangeInStatement`
(M236.013) under the source theorem name in the `Langlands.NYLL` namespace,
under the source's `variable` blocks. The instances of the source's private
M236.002 (`IsAlgClosure k Omega`) and M236.003 (`IsGalois k Omega`), which the
source uses to apply `residueAbsoluteFrobenius_one`, are supplied by local
`have`s, and an `unfold` exposes the target. The source proof is otherwise
kept. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- The compact Frobenius image fixes precisely the finite base field
(M236.013). -/
theorem fixedField_residueAbsoluteFrobeniusRangeIn :
    fixedField_residueAbsoluteFrobeniusRangeInStatement k Omega := by
  have : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  have : IsGalois k Omega := {}
  unfold fixedField_residueAbsoluteFrobeniusRangeInStatement
  apply le_antisymm
  · intro x hx
    have hfrobenius_mem :
        FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ∈
          residueAbsoluteFrobeniusRangeIn k Omega := by
      change FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ∈
        (residueAbsoluteFrobenius k Omega).toMonoidHom.range
      exact ⟨Multiplicative.ofAdd (1 : ZHat),
        residueAbsoluteFrobenius_one k Omega⟩
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxFrobenius := hx
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)
      hfrobenius_mem
    rw [IntermediateField.mem_bot]
    exact (mem_range_algebraMap_iff_frobenius_fixed_in k Omega x).mpr
      hxFrobenius
  · exact bot_le

end
end Langlands.NYLL.LocalClassFieldTheory
