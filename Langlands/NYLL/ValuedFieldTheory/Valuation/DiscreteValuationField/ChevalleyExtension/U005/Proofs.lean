/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 133 (2026-11-13): extract only the proof of M110.005 from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean
(lines 135–154) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published ValuationSubringStatements module
of Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
and state the theorem as that module's `valuationSubring_pullback_of_hasExtension_valuationStatement`
applied to the source binders, opening it with `unfold` before the
unchanged source tactic proof. The unused source universes x y z, the
noncomputable section and the open ResidueField namespace are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements

/-!
# Exact pullback of valuation subrings from `HasExtension` (NYLL M110.005)

If the canonical valuation of a valuation subring `B` of `L` extends `vK`, then
`x : K` maps into `B` exactly when `x` lies in the valuation ring of `vK`.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- A `HasExtension` proof for the canonical valuation attached to a valuation
subring gives exact pullback of valuation subrings. -/
theorem valuationSubring_pullback_of_hasExtension_valuation
    (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)
    [vK.HasExtension B.valuation] (x : K) :
    valuationSubring_pullback_of_hasExtension_valuationStatement vK B x := by
  unfold valuationSubring_pullback_of_hasExtension_valuationStatement
  constructor
  · intro hxB
    have hx_le : B.valuation (algebraMap K L x) ≤ 1 :=
      (B.valuation_le_one_iff (algebraMap K L x)).2 hxB
    have hxK_le : vK x ≤ 1 :=
      (_root_.Valuation.HasExtension.val_map_le_one_iff vK B.valuation x).1 hx_le
    exact (vK.mem_valuationSubring_iff x).1 hxK_le
  · intro hxK
    have hxK_le : vK x ≤ 1 :=
      (vK.mem_valuationSubring_iff x).2 hxK
    have hx_le : B.valuation (algebraMap K L x) ≤ 1 :=
      (_root_.Valuation.HasExtension.val_map_le_one_iff vK B.valuation x).2 hxK_le
    exact (B.valuation_le_one_iff (algebraMap K L x)).1 hx_le

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
