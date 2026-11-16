/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Extracted and adapted by Worker 344, 2026-11-16: the proof of M339.010
(source lines 145–153) of upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; Langlands.NYLL namespace
prefix, a focused import of the published statement, an explicit
fully applied statement target, and new module documentation.
See the paired Markdown for the full record.
The retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Statements

/-!
# Successor recursion for standard Lubin--Tate polynomial iterates

This proves the published M339.010 target using function iteration.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- A successor iterate is obtained by one further composition with the
standard polynomial. -/
theorem standardLubinTatePolynomialIterate_succ
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePolynomialIterate_succStatement F π n := by
  unfold standardLubinTatePolynomialIterate_succStatement
  rw [standardLubinTatePolynomialIterate,
    Function.iterate_succ_apply']
  rfl

end Langlands.NYLL.LubinTate

end
