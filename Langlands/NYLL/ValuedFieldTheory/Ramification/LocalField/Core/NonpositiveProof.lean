/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1237, 2026-11-03, with source extraction, target design
and proof dependency/route analysis contributed by Worker 106:
adapt the proofs of M327.016-M327.020 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 and assemble the closed target
LocalNonpositiveRamificationLawsStatement. Prefix namespaces with
Langlands.NYLL and import the published target and proof inputs. Replace
the global M248.008 extension instance by the local witness of the
published group definitions, and the M327.001 uniqueness alias by the
published chosenLocalExtension_uniqueValuationExtension at comparison
universe 0. Keep M327.016 private, prove the four laws inside the closed
target and restate M327.017-M327.020 as its projections.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.NonpositiveStatement
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.EvaluationProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroupProof

/-!
# Nonpositive local ramification laws: proof

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, M327.016-M327.020
(lines 846-959). The inverse Herbrand function of the actual local
extension fixes every nonpositive real, so upper and lower numbering agree
there; on `(-1, 0]` the real exponent is `1`, so both filtrations equal their
index-zero groups; and at and below `-1` the upper group is full.
-/

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification

/-- M327.016: the actual inverse Herbrand function fixes every nonpositive
real. The extension instance is the local witness of the published groups. -/
private theorem localInverseHerbrandFunction_eq_self_of_nonpos
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) (ht : t ≤ 0) :
    letI : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
        (chosenLocalExtensionCompleteDVF K L).valuation :=
      Classical.choose (chosenLocalExtension_properties K L)
    Higher.inverseHerbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtension_uniqueValuationExtension.{0} K L) t =
      t := by
  let : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  apply
    (Higher.herbrandFunctionOfUniqueExtension_strictMono
      (base := (localCompleteDVF K).toDVF)
      (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
      (chosenLocalExtension_uniqueValuationExtension.{0} K L)).injective
  exact
    (Higher.herbrandFunctionOfUniqueExtension_psi
      (base := (localCompleteDVF K).toDVF)
      (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
      (chosenLocalExtension_uniqueValuationExtension.{0} K L) t).trans
    (DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_of_nonpos
      (Higher.lowerRamificationFiltrationOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtension_uniqueValuationExtension.{0} K L))
      ht).symm

/-- The four nonpositive local ramification laws M327.017-M327.020 at the
exact published closed target. -/
theorem localNonpositiveRamificationLaws :
    LocalNonpositiveRamificationLawsStatement := by
  intro K L _ _ _ _ _ _ _ _
  let : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  -- M327.017: unfold the upper group and use M327.016.
  have hupper : ∀ (t : ℝ), t ≤ 0 →
      localUpperRamificationGroup K L t = localLowerRamificationGroup K L t := by
    intro t ht
    unfold localUpperRamificationGroup localLowerRamificationGroup
    unfold Higher.upperRamificationGroupOfUniqueExtension
    rw [localInverseHerbrandFunction_eq_self_of_nonpos K L t ht]
  -- M327.018: on `(-1, 0]` the real exponent is `1`, as at index zero.
  have hlower : ∀ (t : ℝ), -1 < t → t ≤ 0 →
      localLowerRamificationGroup K L t = localLowerRamificationGroup K L 0 := by
    intro t hneg ht
    have hexp : Higher.realRamificationExponent t = 1 := by
      unfold Higher.realRamificationExponent
      have hceil : Int.ceil (t + 1) = 1 := by
        rw [Int.ceil_eq_iff]
        norm_num
        constructor <;> linarith
      rw [hceil]
      norm_num
    have hideal :
        Higher.realRamificationIdeal
            (chosenLocalExtensionCompleteDVF K L).toDVF t =
          Higher.realRamificationIdeal
            (chosenLocalExtensionCompleteDVF K L).toDVF 0 := by
      unfold Higher.realRamificationIdeal
      have hzero : Higher.realRamificationExponent (0 : ℝ) = 1 := by
        norm_num [Higher.realRamificationExponent]
      rw [hexp, hzero]
    unfold localLowerRamificationGroup
    ext sigma
    change
      (∀ a, _ ∈ Higher.realRamificationIdeal
        (chosenLocalExtensionCompleteDVF K L).toDVF t) ↔
        ∀ a, _ ∈ Higher.realRamificationIdeal
          (chosenLocalExtensionCompleteDVF K L).toDVF 0
    rw [hideal]
  refine ⟨hupper, hlower, ?_, ?_⟩
  · -- M327.019: combine M327.017 at `t` and `0` with M327.018.
    intro t hneg ht
    rw [hupper t ht, hupper 0 le_rfl, hlower t hneg ht]
  · -- M327.020: reduce to the lower group and use its full range.
    intro t ht
    rw [hupper t (by linarith)]
    unfold localLowerRamificationGroup
    exact Higher.lowerRamificationGroup_eq_top_of_le_neg_one
      (chosenLocalExtension_uniqueValuationExtension.{0} K L) ht

/-- M327.017: at every nonpositive index the inverse Herbrand function is the
identity, so upper and lower numbering agree. -/
theorem localUpperRamificationGroup_eq_localLowerRamificationGroup_of_nonpos
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) (ht : t ≤ 0) :
    localUpperRamificationGroup K L t =
      localLowerRamificationGroup K L t :=
  (localNonpositiveRamificationLaws K L).1 t ht

/-- M327.018: the lower filtration is constant between the distinguished
endpoints `-1` and `0`: every such real index imposes exactly the first
maximal-ideal power, so the group equals its index-zero group. -/
theorem localLowerRamificationGroup_eq_zero_of_neg_one_lt_of_nonpos
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) (hneg : -1 < t) (ht : t ≤ 0) :
    localLowerRamificationGroup K L t =
      localLowerRamificationGroup K L 0 :=
  (localNonpositiveRamificationLaws K L).2.1 t hneg ht

/-- M327.019: the upper filtration is constant on the half-open interval
`(-1, 0]`, equal to its index-zero group. -/
theorem localUpperRamificationGroup_eq_zero_of_neg_one_lt_of_nonpos
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) (hneg : -1 < t) (ht : t ≤ 0) :
    localUpperRamificationGroup K L t =
      localUpperRamificationGroup K L 0 :=
  (localNonpositiveRamificationLaws K L).2.2.1 t hneg ht

/-- M327.020: at and below `-1`, the local upper ramification group is the
full Galois group. -/
theorem localUpperRamificationGroup_eq_top_of_le_neg_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) (ht : t ≤ -1) :
    localUpperRamificationGroup K L t = ⊤ :=
  (localNonpositiveRamificationLaws K L).2.2.2 t ht

end Langlands.NYLL.RamificationTheory.LocalField
