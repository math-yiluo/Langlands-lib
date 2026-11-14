/-
NYLL source: Copyright (c) 2026 Naganori Yamaguchi
(https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0; Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
Pinned commit: fbd320cd8b1b06487c58227e92eb135794267709.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.

Worker 296, 2026-11-13: derive an internal comparison with the published FLT
ring-action formalization, reusing Library declarations by Lean name. This is
an alternate proof route to NYLL M327.009, not a translation of M326. The
published HerbrandBridge transport and finite-sum helpers are reused directly;
its fixed-subring strategy is adapted to the NYLL chosen-valuation convention.
The FLT theorem attribution and notices remain in licenses/Anthropic-FLT/.
See the paired Markdown for the complete proof route and source correspondence.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.FLTComparison
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.NonpositiveProof
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

noncomputable section
set_option linter.style.haveILetI false

namespace Langlands.NYLL.PortInternal.FltBridge

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
open Langlands.NYLL.RamificationTheory.LocalField
open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

abbrev chosenRing := (chosenLocalExtensionCompleteDVF K L).valuationSubring

abbrev chosenAction : MulSemiringAction Gal(L/K) (chosenRing K L) :=
  letI : (localCompleteDVF K).valuation.HasExtension
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  valuationAction (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtension_uniqueValuationExtension.{0} K L)

theorem chosenResidueFinite : Finite
    (chosenRing K L ⧸ IsLocalRing.maximalIdeal (chosenRing K L)) := by
  let base := localCompleteDVF K
  let target := chosenLocalExtensionCompleteDVF K L
  let : base.valuation.HasExtension target.valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  haveI : Module.Finite base.valuationSubring target.valuationSubring :=
    (Classical.choose_spec (chosenLocalExtension_properties K L)).2
  exact IsLocalRing.ResidueField.finite_of_finite
    (R := base.valuationSubring) (S := target.valuationSubring)
    (inferInstanceAs (Finite 𝓀[K]))

theorem source_lower_map (H : Subgroup Gal(L/K)) [H.Normal] (n : ℕ) :
    letI := chosenAction K L
    (IsLocalRing.lowerRamificationGroup (chosenRing K L) Gal(L/K) n).map
      (QuotientGroup.mk' H) =
    IsLocalRing.lowerRamificationGroup (FixedPoints.subring (chosenRing K L) H)
      (Gal(L/K) ⧸ H) ⌈IsLocalRing.herbrandPhi (chosenRing K L) H (n : ℚ)⌉₊ := by
  letI := chosenAction K L
  letI : (localCompleteDVF K).valuation.HasExtension
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  haveI := action_faithful (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtension_uniqueValuationExtension.{0} K L)
  haveI := chosenResidueFinite K L
  haveI : (IsLocalRing.maximalIdeal (chosenRing K L)).LiesOver
      (IsLocalRing.maximalIdeal (FixedPoints.subring (chosenRing K L) Gal(L/K))) :=
    ⟨FixedPoints.maximalIdeal_subring_eq_comap⟩
  letI : Field (chosenRing K L ⧸ IsLocalRing.maximalIdeal (chosenRing K L)) :=
    Ideal.Quotient.field _
  letI : Field (FixedPoints.subring (chosenRing K L) Gal(L/K) ⧸
      IsLocalRing.maximalIdeal (FixedPoints.subring (chosenRing K L) Gal(L/K))) :=
    Ideal.Quotient.field _
  haveI : Finite (FixedPoints.subring (chosenRing K L) Gal(L/K) ⧸
      IsLocalRing.maximalIdeal (FixedPoints.subring (chosenRing K L) Gal(L/K))) :=
    Finite.of_injective (algebraMap _
      (chosenRing K L ⧸ IsLocalRing.maximalIdeal (chosenRing K L)))
      (algebraMap
        (FixedPoints.subring (chosenRing K L) Gal(L/K) ⧸
          IsLocalRing.maximalIdeal (FixedPoints.subring (chosenRing K L) Gal(L/K)))
        (chosenRing K L ⧸ IsLocalRing.maximalIdeal (chosenRing K L))).injective
  exact IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField n

theorem chosen_mem_iff (E : IntermediateField K L) [IsGalois K E] (a : E) :
    a ∈ (chosenLocalExtensionCompleteDVF K E).valuation.valuationSubring ↔
      (a : L) ∈ (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring := by
  let base := localCompleteDVF K
  let targetE := chosenLocalExtensionCompleteDVF K E
  let targetL := chosenLocalExtensionCompleteDVF K L
  let : base.valuation.HasExtension targetE.valuation :=
    Classical.choose (chosenLocalExtension_properties K E)
  let : base.valuation.HasExtension targetL.valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  let pulled := targetL.valuation.comap E.val.toRingHom
  let : base.valuation.HasExtension pulled :=
    { val_isEquiv_comap := by
        rw [_root_.Valuation.isEquiv_iff_val_le_one]
        intro k
        change base.valuation k ≤ 1 ↔ targetL.valuation (algebraMap K L k) ≤ 1
        exact (_root_.Valuation.HasExtension.val_map_le_one_iff
          (vR := base.valuation) (vA := targetL.valuation) k).symm }
  let hu : Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
      base.toDVF targetE.toDVF := chosenLocalExtension_uniqueValuationExtension.{0} K E
  exact _root_.Valuation.isEquiv_iff_val_le_one.mp (hu pulled)

def fixedRingEquiv (H : Subgroup Gal(L/K)) [H.Normal] :
    letI := chosenAction K L
    FixedPoints.subring (chosenRing K L) H ≃+* chosenRing K (IntermediateField.fixedField H) := by
  letI := chosenAction K L
  exact
  { toFun x := ⟨⟨((x : chosenRing K L) : L), fun h => congrArg Subtype.val (x.2 h)⟩,
      (chosen_mem_iff K L (IntermediateField.fixedField H) _).mpr (x : chosenRing K L).2⟩
    invFun y := ⟨⟨((y : IntermediateField.fixedField H) : L),
      (chosen_mem_iff K L (IntermediateField.fixedField H) _).mp y.2⟩,
      fun h => Subtype.ext ((y : IntermediateField.fixedField H).2 h)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl }

theorem fixedRingEquiv_smul (H : Subgroup Gal(L/K)) [H.Normal] (g : Gal(L/K))
    (a : letI := chosenAction K L; FixedPoints.subring (chosenRing K L) H) :
    letI := chosenAction K L
    letI := chosenAction K (IntermediateField.fixedField H)
    fixedRingEquiv K L H ((QuotientGroup.mk g : Gal(L/K) ⧸ H) • a) =
      AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) g •
        fixedRingEquiv K L H a := by
  letI := chosenAction K L
  letI := chosenAction K (IntermediateField.fixedField H)
  apply Subtype.ext
  apply Subtype.ext
  exact (AlgEquiv.restrictNormalHom_apply (IntermediateField.fixedField H) g
    ⟨((a : chosenRing K L) : L), fun h => congrArg Subtype.val (a.2 h)⟩).symm

theorem local_upper_rat_eq (q : ℚ) (hq : 0 ≤ q) :
    letI := chosenAction K L
    localUpperRamificationGroup K L (q : ℝ) =
      IsLocalRing.upperRamificationGroup (chosenRing K L) Gal(L/K) q := by
  letI : (localCompleteDVF K).valuation.HasExtension
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  exact upper_rat_eq (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtension_uniqueValuationExtension.{0} K L) q hq

theorem local_exists_rat_upper_const {t : ℝ} (ht : 0 ≤ t) :
    ∃ q : ℚ, 0 ≤ q ∧ t ≤ q ∧ ∀ s : ℝ, t ≤ s → s ≤ q →
      localUpperRamificationGroup K L s = localUpperRamificationGroup K L t := by
  letI : (localCompleteDVF K).valuation.HasExtension
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  exact exists_rat_upper_const (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtension_uniqueValuationExtension.{0} K L) ht

theorem local_map_fixed_rat (H : Subgroup Gal(L/K)) [H.Normal] (q : ℚ) (hq : 0 ≤ q) :
    (localUpperRamificationGroup K L (q : ℝ)).map
      (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H)) =
      localUpperRamificationGroup K (IntermediateField.fixedField H) (q : ℝ) := by
  letI := chosenAction K L
  letI := chosenAction K (IntermediateField.fixedField H)
  let f : (Gal(L/K) ⧸ H) ≃* Gal(IntermediateField.fixedField H/K) :=
    IsGalois.normalAutEquivQuotient H
  have hf : AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) =
      (f : _ →* _).comp (QuotientGroup.mk' H) :=
    MonoidHom.ext fun g => (IsGalois.normalAutEquivQuotient_apply H g).symm
  have he : ∀ (g : Gal(L/K) ⧸ H) (a : FixedPoints.subring (chosenRing K L) H),
      fixedRingEquiv K L H (g • a) = f g • fixedRingEquiv K L H a := by
    intro g a
    induction g using QuotientGroup.induction_on with
    | H g => exact fixedRingEquiv_smul K L H g a
  rw [local_upper_rat_eq K L q hq,
    local_upper_rat_eq K (IntermediateField.fixedField H) q hq,
    hf, ← Subgroup.map_map,
    IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
      (source_lower_map K L H) q hq]
  exact upper_of_equivariant (fixedRingEquiv K L H) f he q

theorem local_map_fixed (H : Subgroup Gal(L/K)) [H.Normal] (t : ℝ) :
    (localUpperRamificationGroup K L t).map
      (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H)) =
      localUpperRamificationGroup K (IntermediateField.fixedField H) t := by
  by_cases ht : 0 ≤ t
  · obtain ⟨qL, hqL, htqL, hL⟩ := local_exists_rat_upper_const K L ht
    obtain ⟨qE, hqE, htqE, hE⟩ :=
      local_exists_rat_upper_const K (IntermediateField.fixedField H) ht
    have htq : t ≤ ((min qL qE : ℚ) : ℝ) := by
      push_cast
      exact le_min htqL htqE
    rw [← hL _ htq (by push_cast; exact min_le_left _ _),
      ← hE _ htq (by push_cast; exact min_le_right _ _)]
    exact local_map_fixed_rat K L H (min qL qE) (le_min hqL hqE)
  · by_cases hneg : t ≤ -1
    · rw [localUpperRamificationGroup_eq_top_of_le_neg_one K L t hneg,
        localUpperRamificationGroup_eq_top_of_le_neg_one K (IntermediateField.fixedField H) t hneg,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact AlgEquiv.restrictNormalHom_surjective _
    · rw [localUpperRamificationGroup_eq_zero_of_neg_one_lt_of_nonpos K L t
          (lt_of_not_ge hneg) (le_of_not_ge ht),
        localUpperRamificationGroup_eq_zero_of_neg_one_lt_of_nonpos K
          (IntermediateField.fixedField H) t (lt_of_not_ge hneg) (le_of_not_ge ht)]
      simpa only [Rat.cast_zero] using local_map_fixed_rat K L H 0 le_rfl

end Langlands.NYLL.PortInternal.FltBridge
