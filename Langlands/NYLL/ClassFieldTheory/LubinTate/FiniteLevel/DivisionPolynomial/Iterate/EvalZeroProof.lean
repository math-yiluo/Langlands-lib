/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 311, 2026-11-16: extract M339.013 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 into a focused proof module;
use the published Langlands.NYLL statement as the exact theorem type,
and derive successor recursion locally from the published iterate definition.
See the paired Markdown for the proof and modification record.
The retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Statements

/-!
# Vanishing at zero of standard Lubin--Tate polynomial iterates

This module proves the published M339.013 target at its full telescope.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Every standard compositional iterate vanishes at zero. -/
@[simp]
theorem standardLubinTatePolynomialIterate_eval_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePolynomialIterate_eval_zeroStatement F π n := by
  change (standardLubinTatePolynomialIterate F π n).eval 0 = 0
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      have hsucc :
          standardLubinTatePolynomialIterate F π (n + 1) =
            (standardLubinTatePolynomial F π).comp
              (standardLubinTatePolynomialIterate F π n) := by
        rw [standardLubinTatePolynomialIterate, Function.iterate_succ_apply']
        rfl
      rw [hsucc, Polynomial.eval_comp, ih]
      simp [standardLubinTatePolynomial,
        ne_of_gt
          (Nat.zero_lt_one.trans
            (Finite.one_lt_card : 1 < Nat.card F.residueField))]

end Langlands.NYLL.LubinTate

end
