/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 678, 2026-11-16, using Worker 495's trial proof:
extract M351.027, source lines 829-839 of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
commit fbd320cd8b1b06487c58227e92eb135794267709. Rename the source-private
theorem as Langlands.NYLL.PortInternal.M351.d027 and state its type using
the published d027Statement target. Replace the original imports by the
focused published statement module, unfold that target before the original
proof, and omit unused source context. Preserve the exact source binders.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.Statements

/-!
# A linear form is a sum of degree-one monomials

Proof of the published target for NYLL M351.027, by rewriting each product
of a constant series and a variable as a single monomial.
-/

universe u v w

namespace Langlands.NYLL

open LubinTate LubinTate.SameUniformizer
open LocalFieldTheory.DiscreteValuationField

namespace PortInternal.M351

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {σ : Type w} [Fintype σ]

/-- NYLL M351.027: the linear form is the sum of its degree-one monomials. -/
theorem d027 (L : σ → F.valuationSubring) : d027Statement L := by
  rw [d027Statement, linearForm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.X_def,
    MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]

end PortInternal.M351

end Langlands.NYLL
