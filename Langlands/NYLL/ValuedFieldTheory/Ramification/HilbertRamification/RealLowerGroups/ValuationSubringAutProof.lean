/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with source extraction, grouped target,
parameter and elementary proof-route analysis contributed by Worker 106:
isolate M304.015–.021 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, import the published closed statement and its actual
objects, retain the seven source proofs and assemble the exact closed
four-universe conjunction. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAutStatement

/-!
# Valuation-ring automorphism properties from unique extension

The seven elementary laws M304.015–.021 of the pinned NYLL
`RealLowerGroups.lean`, assembled as the exact published closed proposition.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

open Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF

section Properties

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- States the theorem `valuationSubringAutOfUniqueExtension_apply_coe`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_apply_coe
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    ((valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ a :
        target.valuationSubring) : L) = σ (a : L) :=
  rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_one_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_one_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq 1 a = a := Subtype.ext rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_mul_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_mul_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ τ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq (σ * τ) a =
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ a) := by
  ext
  rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_apply_inv_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_apply_inv_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ⁻¹ a) = a := Subtype.ext (σ.apply_symm_apply a)

/-- A uniquely extended valuation-ring automorphism preserves the maximal
ideal. -/
theorem valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ↔
      a ∈ target.maximalIdeal := by
  let e := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq σ
  change e a ∈ target.maximalIdeal ↔ a ∈ target.maximalIdeal
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hea ha
    exact hea (by simpa using ha.map (e : target.valuationSubring →* target.valuationSubring))
  · intro ha hea
    exact ha (by simpa using hea.map (e.symm : target.valuationSubring →* target.valuationSubring))

/-- A uniquely extended valuation-ring automorphism preserves every power of
the maximal ideal. -/
theorem valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (n : ℕ) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ^ n ↔
      a ∈ target.maximalIdeal ^ n := by
  let e := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq σ
  have hm :
      Ideal.map (e : target.valuationSubring →+* target.valuationSubring)
          target.maximalIdeal = target.maximalIdeal := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target.valuationSubring) e.surjective]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
          (base := base) (target := target) huniq σ b).2 hb
    · intro ha
      refine ⟨e.symm a, ?_, by simp [e]⟩
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
          (base := base) (target := target) huniq σ (e.symm a)).1
          (by simpa [e] using ha)
  have hmap :
      Ideal.map (e : target.valuationSubring →+* target.valuationSubring)
          (target.maximalIdeal ^ n) = target.maximalIdeal ^ n := by
    rw [Ideal.map_pow, hm]
  constructor
  · intro ha
    rw [← hmap] at ha
    rcases (Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target.valuationSubring) e.surjective).1 ha with
      ⟨b, hb, hba⟩
    have : b = a := e.injective hba
    simpa [this] using hb
  · intro ha
    rw [← hmap]
    exact Ideal.mem_map_of_mem
      (e : target.valuationSubring →+* target.valuationSubring) ha

/-- States the theorem `valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff`. -/
theorem valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (s : ℝ) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈
          realRamificationIdeal target s ↔
      a ∈ realRamificationIdeal target s := by
  exact valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
    (base := base) (target := target) huniq σ
      (realRamificationExponent s) a

end Properties

/-- The complete closed valuation-ring automorphism property target. -/
theorem valuationSubringAutProperties :
    ValuationSubringAutPropertiesStatement.{u, v, w, x} := by
  intro K L _ _ _ base target _ huniq
  exact ⟨valuationSubringAutOfUniqueExtension_apply_coe (base := base) (target := target) huniq,
    valuationSubringAutOfUniqueExtension_one_apply (base := base) (target := target) huniq,
    valuationSubringAutOfUniqueExtension_mul_apply (base := base) (target := target) huniq,
    valuationSubringAutOfUniqueExtension_apply_inv_apply (base := base) (target := target) huniq,
    valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff (base := base) (target := target) huniq,
    valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff (base := base) (target := target) huniq,
    valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff (base := base) (target := target) huniq⟩

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
