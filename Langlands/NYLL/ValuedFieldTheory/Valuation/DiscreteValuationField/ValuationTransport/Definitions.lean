/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 202, 13 November 2026: extract the listed data from
upstream fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, and reduce imports. See the paired Markdown for the exact
correspondence and modification record. LICENSE and NOTICE are retained
under licenses/NYLL/.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

universe u v w

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]

noncomputable def valuationSubringRingEquivOfComap
    (v : _root_.Valuation K Γ) (e : L ≃+* K) :
    (v.comap (e : L →+* K)).valuationSubring ≃+* v.valuationSubring where
  toFun x := ⟨e (x : L), x.2⟩
  invFun y := ⟨e.symm (y : K), by
    change v (e (e.symm (y : K))) ≤ 1
    rw [e.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : L))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : K))
  map_mul' x y := Subtype.ext (map_mul e (x : L) (y : L))
  map_add' x y := Subtype.ext (map_add e (x : L) (y : L))

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
