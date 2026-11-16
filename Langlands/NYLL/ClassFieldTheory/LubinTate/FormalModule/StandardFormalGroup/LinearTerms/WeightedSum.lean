/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 497, 2026-11-14: port the proof of the private
source theorem LubinTate.SameUniformizer.HasLinearTerm.linearForm_weighted_sum
(M354.003, source lines 76-86 of StandardFormalGroup.lean, upstream commit
fbd320cd8b1b06487c58227e92eb135794267709) as the public theorem
Langlands.NYLL.PortInternal.M354.d003 proving the published target
d003Statement.
The original LICENSE and NOTICE remain in licenses/NYLL/.

Prepared by Worker 338, 2026-11-16: reuse Worker 497's shared draft
revision 1 without changing the theorem or proof; complete the paired
Markdown extraction and adaptation record for focused submission.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements

/-!
# M354.003: a weighted sum of linear forms is a linear form

Proof of `Langlands.NYLL.PortInternal.M354.d003Statement`.
-/

open scoped BigOperators

universe w w'

namespace Langlands.NYLL.PortInternal.M354

open Langlands.NYLL.LubinTate.SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]
variable {τ : Type w'} [Fintype τ]

/-- A weighted sum of linear forms is the linear form of the weighted
coefficients (NYLL M354.003, private in the source). -/
theorem d003 (L : σ → R) (M : σ → τ → R) : d003Statement L M := by
  classical
  apply MvPowerSeries.ext
  intro d
  simp only [linearForm, map_sum, MvPowerSeries.coeff_C_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end Langlands.NYLL.PortInternal.M354
