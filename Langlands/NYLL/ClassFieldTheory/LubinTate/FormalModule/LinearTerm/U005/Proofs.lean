/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 465 on 2026-11-14: extracted the proof of M347.005
(theorem `hasSubst`, lines 44 and 56–60) from
Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean at commit
fbd320cd8b1b06487c58227e92eb135794267709, prefixed the namespace with
Langlands.NYLL and stated the theorem as the published
`HasLinearTerm.hasSubstStatement h`, opened by `unfold`. The source term
`h.constantCoeff_eq_zero` (M347.004) is replaced by that theorem's source
tactic proof (lines 50–54) as a local step, with its `simp` lemma
`constantCoeff_linearForm` (M347.002) replaced by unfolding `linearForm`
(its source proof, line 35), because neither theorem is in this Library
base. Details are in the paired Markdown; LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Statements

/-!
# Substitution for series with a prescribed linear term (NYLL M347.005)

A multivariable power series whose difference from a linear form has total
order at least two has zero constant coefficient, so it can be substituted
into a one-variable power series.
-/

namespace Langlands.NYLL.LubinTate.SameUniformizer

universe u v

variable {R : Type u} [CommRing R]
variable {σ : Type v} [Fintype σ]

namespace HasLinearTerm

variable {H : MvPowerSeries σ R} {L : σ → R}

/-- Consequently the series can genuinely be substituted into a
one-variable power series. -/
theorem hasSubst (h : HasLinearTerm H L) :
    HasLinearTerm.hasSubstStatement h := by
  unfold HasLinearTerm.hasSubstStatement
  -- Source lines 50–54 (M347.004), with `linearForm` unfolded in place of
  -- the M347.002 simp lemma `constantCoeff_linearForm`.
  have horder : (1 : ℕ∞) ≤ (H - linearForm L).order :=
    (by norm_num : (1 : ℕ∞) ≤ 2).trans h
  have hconstant :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp horder
  have hH : MvPowerSeries.constantCoeff H = 0 := by
    simpa [linearForm] using hconstant
  -- Source line 60.
  exact PowerSeries.HasSubst.of_constantCoeff_zero hH

end HasLinearTerm

end Langlands.NYLL.LubinTate.SameUniformizer
