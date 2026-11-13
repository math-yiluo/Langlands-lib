/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 133 (2026-11-13): extract only the proof of M110.002 from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean
(lines 47–85) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published ValuationSubringStatements module
of Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
and state the theorem as that module's `mem_base_valuationSubring_of_lift_memStatement`
applied to the source binders, opening it with `unfold` before the
unchanged source tactic proof. The unused source universes x y z, the
noncomputable section and the open ResidueField namespace are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements

/-!
# Base-field membership from a locally dominating valuation subring (NYLL M110.002)

If a valuation subring `B` of `L` contains the image of the valuation ring of
`vK` and the induced ring map is local, then any `x : K` whose image lies in
`B` already lies in the valuation ring of `vK`.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- If a valuation subring `B` of the extension field dominates the base
valuation ring locally, then any base-field element whose image lies in `B`
already lies in the base valuation ring. -/
theorem mem_base_valuationSubring_of_lift_mem
    (vK : _root_.Valuation K ΓK)
    (B : ValuationSubring L)
    (hB : ∀ x : vK.valuationSubring, algebraMap vK.valuationSubring L x ∈ B.toSubring)
    (hlocal : IsLocalHom
      ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB))
    {x : K} (hxB : algebraMap K L x ∈ B.toSubring) :
    mem_base_valuationSubring_of_lift_memStatement vK B hB hlocal hxB := by
  unfold mem_base_valuationSubring_of_lift_memStatement
  let A := vK.valuationSubring
  rcases A.mem_or_inv_mem x with hxA | hxinvA
  · exact hxA
  · by_cases hx0 : x = 0
    · simp [hx0]
    let y : A := ⟨x⁻¹, hxinvA⟩
    let f : A →+* B.toSubring :=
      (algebraMap A L).codRestrict B.toSubring hB
    let : IsLocalHom f := by
      dsimp [f, A]
      exact hlocal
    have hfy_unit : IsUnit (f y) := by
      apply IsUnit.of_mul_eq_one (⟨algebraMap K L x, hxB⟩ : B.toSubring)
      ext
      change (algebraMap K L) (x⁻¹) * (algebraMap K L) x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hy_unit : IsUnit y := IsUnit.of_map f y hfy_unit
    have hy_val : A.valuation (x⁻¹) = 1 := by
      simpa [y] using (A.valuation_eq_one_iff y).1 hy_unit
    have hx_val : A.valuation x = 1 := by
      rw [← inv_inv x, map_inv₀, hy_val, inv_one]
    exact A.mem_of_valuation_le_one x hx_val.le

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
