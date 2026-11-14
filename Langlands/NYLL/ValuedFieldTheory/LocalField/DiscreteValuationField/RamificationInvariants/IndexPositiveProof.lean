/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 308, 2026-11-13: adapt the selected source result at
commit fbd320cd8b1b06487c58227e92eb135794267709 to its published Langlands.NYLL
Statement target. Reuse the published CompleteDVF projections and exact
Mathlib bodies of M108.003/.005. See the paired Markdown for the proof route,
source correspondence and modifications. Retained license and notices are
in licenses/NYLL/.

Modified by Worker 426, 2026-11-14: add the module and theorem docstrings;
the proof is Worker 308's design, unchanged.
-/
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants.IndexStatements

/-!
# Positivity of the canonical ramification index

This module proves the published proposition
`ramificationIndex_posStatement`, adapted from M343.003 (`ramificationIndex_pos`) in
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/RamificationInvariants.lean`.
The proof inlines the nonvanishing argument through Mathlib's Dedekind-domain
lemma `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`.
-/

noncomputable section
universe u v w x
namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
variable [base.valuation.HasExtension target.valuation]

/-- For an extension of complete discretely valued fields whose valuation subrings form a
torsion-free module, the canonical ideal ramification index
`Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal` is positive. -/
theorem ramificationIndex_pos
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    ramificationIndex_posStatement base target := by
  apply Nat.pos_of_ne_zero
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    target.maximalIdeal (IsDiscreteValuationRing.not_a_field base.valuationSubring)

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
