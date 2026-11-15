/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Initial.Statements

/-!
# Finite local reciprocity: Frobenius-fixed points of a residue algebraic closure (proof)

Modified by Worker 46: prove the published target
`Langlands.NYLL.LocalClassFieldTheory.mem_range_algebraMap_iff_frobenius_fixed_inStatement`
(M236.011) under the source theorem name in the `Langlands.NYLL` namespace,
under the source's `variable` blocks and its `omit [IsAlgClosed Omega]`. The
source proof is kept. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

omit [IsAlgClosed Omega] in
/-- In any algebraic closure of a finite field, the fixed points of arithmetic
Frobenius are exactly the base field (M236.011). -/
theorem mem_range_algebraMap_iff_frobenius_fixed_in
    (x : Omega) :
    mem_range_algebraMap_iff_frobenius_fixed_inStatement k Omega x := by
  unfold mem_range_algebraMap_iff_frobenius_fixed_inStatement
  constructor
  · rintro ⟨a, rfl⟩
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have hxpow : x ^ Fintype.card k = x := by
      simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using hx
    let p : k[X] := X ^ Fintype.card k - X
    have hpne : p ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hxroot : x ∈ p.rootSet Omega := by
      rw [Polynomial.mem_rootSet_of_ne hpne]
      simp [p, hxpow]
    have hsplits : (p.map (algebraMap k k)).Splits := by
      simpa only [p] using (FiniteField.isSplittingField_sub k k).splits
    have himage := hsplits.image_rootSet (Algebra.ofId k Omega)
    rw [← himage] at hxroot
    rcases hxroot with ⟨a, _ha, hax⟩
    exact ⟨a, hax⟩

end
end Langlands.NYLL.LocalClassFieldTheory
