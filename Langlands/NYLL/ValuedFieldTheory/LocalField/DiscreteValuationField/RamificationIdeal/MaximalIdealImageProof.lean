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
-/
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal.ImageStatements
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

noncomputable section
universe u v w x
namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
variable [base.valuation.HasExtension target.valuation]

theorem maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex :
    maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndexStatement base target := by
  change Ideal.map (algebraMap base.valuationSubring target.valuationSubring) base.maximalIdeal =
    target.maximalIdeal ^ Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal
  have hne :
      Ideal.map ((algebraMap base.valuationSubring target.valuationSubring)) base.maximalIdeal ≠ ⊥ := by
    exact (Ideal.map_eq_bot_iff_of_injective
      (_root_.Valuation.HasExtension.algebraMap_injective
        (vK := base.valuation) (vA := target.valuation))).not.mpr
      (IsDiscreteValuationRing.not_a_field base.valuationSubring)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal
    target.valuationSubring (inferInstance : target.maximalIdeal.IsPrincipal)
    (Ideal.map ((algebraMap base.valuationSubring target.valuationSubring)) base.maximalIdeal) hne
  have hnot : ¬ target.maximalIdeal ^ n ≤ target.maximalIdeal ^ (n + 1) :=
    not_le_of_gt (target.maximalIdeal.pow_right_strictAnti
      (IsDiscreteValuationRing.not_a_field target.valuationSubring)
      (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).ne_top
      (Nat.lt_succ_self n))
  have he : (Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal) = n := by
    apply Ideal.ramificationIdx'_spec (le_of_eq hn)
    change ¬ Ideal.map ((algebraMap base.valuationSubring target.valuationSubring)) base.maximalIdeal ≤
      target.maximalIdeal ^ (n + 1)
    rwa [hn]
  rw [he]
  exact hn

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
