/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 308, 2026-11-13: adapt the selected source result at
commit fbd320cd8b1b06487c58227e92eb135794267709 to its published Langlands.NYLL
Statement target. Reuse the published CompleteDVF projections and exact
Mathlib bodies of M108.003/.005.
Modified by Worker 430, 2026-11-14: replace the use of the maximal-ideal image
identity (M344.002) and the maximal-ideal inclusion wrapper by a direct
computation of the mapped base uniformizer's additive valuation from
Mathlib's DVR divisibility criterion, `Ideal.ramificationIdx'_spec` and the
local-homomorphism instance of the valuation-subring algebra map.
See the paired Markdown for the proof route, source correspondence and
modifications. Retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal.RestrictionStatements

noncomputable section
universe u v w x
namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The target normalized additive valuation of the image of a base integer is
the canonical ramification index times its base normalized additive valuation;
this includes `a = 0`, where both sides are `⊤`. -/
theorem addVal_integerMap_eq_ramificationIndex_nsmul
    (a : base.valuationSubring) :
    addVal_integerMap_eq_ramificationIndex_nsmulStatement base target a := by
  change IsDiscreteValuationRing.addVal target.valuationSubring
    (algebraMap base.valuationSubring target.valuationSubring a) =
    Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal •
      IsDiscreteValuationRing.addVal base.valuationSubring a
  set f := algebraMap base.valuationSubring target.valuationSubring
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible base.valuationSubring
  obtain ⟨varpi, hvarpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  -- The image of the base uniformizer is nonzero, by injectivity of `f`.
  have hfpi0 : f pi ≠ 0 := by
    intro h
    apply hpi.ne_zero
    apply _root_.Valuation.HasExtension.algebraMap_injective
      (vK := base.valuation) (vA := target.valuation)
    exact h.trans (map_zero f).symm
  obtain ⟨k, u, hk⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfpi0 hvarpi
  have hval_fpi : IsDiscreteValuationRing.addVal target.valuationSubring (f pi) = k :=
    IsDiscreteValuationRing.addVal_def _ u hvarpi k hk
  -- The mapped base maximal ideal lies in the `n`-th target power exactly when `n ≤ k`.
  have hle (n : ℕ) :
      Ideal.map f base.maximalIdeal ≤ target.maximalIdeal ^ n ↔ n ≤ k := by
    rw [show base.maximalIdeal = IsLocalRing.maximalIdeal base.valuationSubring from rfl,
      hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      show target.maximalIdeal = IsLocalRing.maximalIdeal target.valuationSubring from rfl,
      hvarpi.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton,
      ← IsDiscreteValuationRing.addVal_le_iff_dvd, hvarpi.addVal_pow, hval_fpi]
    exact Nat.cast_le
  have he : Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal = k :=
    Ideal.ramificationIdx'_spec ((hle k).2 le_rfl)
      (fun h => Nat.not_succ_le_self k ((hle (k + 1)).1 h))
  rw [he]
  -- The image of the base uniformizer is not a unit, so `k ≠ 0`.
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hpi.not_isUnit
    apply (isUnit_map_iff f pi).mp
    rw [hk, pow_zero, mul_one]
    exact u.isUnit
  by_cases ha : a = 0
  · subst a
    have hk0' : (k : ℕ∞) ≠ 0 := by exact_mod_cast hk0
    rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero,
      nsmul_eq_mul, ENat.mul_top hk0']
  obtain ⟨m, unit, ha_decomp⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hpi
  have hmap_unit :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (f (unit : base.valuationSubring)) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (unit.isUnit.map f)
  rw [IsDiscreteValuationRing.addVal_def a unit hpi m ha_decomp, ha_decomp, map_mul,
    map_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    hmap_unit, hval_fpi, zero_add, nsmul_eq_mul, nsmul_eq_mul, mul_comm]

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.ValuedExtension
