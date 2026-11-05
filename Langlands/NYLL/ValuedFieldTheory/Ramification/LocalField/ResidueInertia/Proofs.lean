/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1612, 2026-11-04, with source extraction, target design
and proof-route analysis contributed by Worker 106: adapt M328.001 and
M328.002 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709,
prove the exact closed published target and expose both source-name
consequences. Compare the chosen valuation ring directly with the supplied
integer ring, keeping the published chosen uniqueness witness and a local
extension instance. Use the proved integer-ring restriction evaluation.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.ResidueInertia.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenSuppliedComparisonProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.KernelProofs
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.NonpositiveProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAutProof

/-!
# Zero-depth local ramification and the actual residue-action kernel

The chosen valuation ring and the supplied integer ring agree inside `L`.
Their identity ring equivalence transports maximal-ideal membership and
the automorphism displacement condition. Upper numbering at zero then
agrees with lower numbering by the published nonpositive law.
-/

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification
open scoped ValuativeRel

/-- Both actual local ramification groups at zero equal the kernel of the
actual supplied residue action, with all source hypotheses internal. -/
theorem localRamificationZeroResidueKernel :
    LocalRamificationZeroResidueKernelStatement := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _
  let : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  have hInteger : target.valuation.valuationSubring.toSubring =
      (ValuativeRel.valuation L).integer :=
    congrArg ValuationSubring.toSubring (chosenLocalExtension_suppliedComparison K L).2
  let eInteger : target.valuationSubring ≃+* 𝒪[L] :=
    RingEquiv.subringCongr hInteger
  have hmap (σ : Gal(L/K)) (a : target.valuationSubring) :
      eInteger (Higher.valuationSubringAutOfUniqueExtension
        (base := (localCompleteDVF K).toDVF) (target := target)
        (chosenLocalExtension_uniqueValuationExtension.{0} K L) σ a - a) =
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (eInteger a) -
        eInteger a := by
    apply Subtype.ext
    change ((Higher.valuationSubringAutOfUniqueExtension
        (base := (localCompleteDVF K).toDVF) (target := target)
        (chosenLocalExtension_uniqueValuationExtension.{0} K L) σ a :
        target.valuationSubring) : L) - (a : L) =
      ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (eInteger a) :
        𝒪[L]) : L) - (eInteger a : L)
    rw [Higher.valuationSubringAutOfUniqueExtension_apply_coe
        (base := (localCompleteDVF K).toDVF) (target := target)
        (chosenLocalExtension_uniqueValuationExtension.{0} K L) σ a,
      galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L σ (eInteger a)]
    rfl
  have hmem (a : target.valuationSubring) :
      eInteger a ∈ (𝓂[L] : Ideal 𝒪[L]) ↔ a ∈ target.maximalIdeal := by
    rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff eInteger,
      ← IsLocalRing.mem_maximalIdeal]
  have hlower : localLowerRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
    apply Subgroup.ext
    intro σ
    rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal]
    have hzero := Higher.mem_lowerRamificationGroup_nat_iff
      (base := (localCompleteDVF K).toDVF) (target := target)
      (chosenLocalExtension_uniqueValuationExtension.{0} K L) 0 σ
    simp only [Nat.cast_zero, Nat.zero_add, pow_one] at hzero
    change σ ∈ Higher.lowerRamificationGroup
      (base := (localCompleteDVF K).toDVF) (target := target)
      (chosenLocalExtension_uniqueValuationExtension.{0} K L) 0 ↔ _
    rw [hzero]
    constructor
    · intro h x
      obtain ⟨a, rfl⟩ := eInteger.surjective x
      rw [← hmap, hmem]
      exact h a
    · intro h a
      apply (hmem _).mp
      rw [hmap]
      exact h (eInteger a)
  refine ⟨hlower, ?_⟩
  rw [localUpperRamificationGroup_eq_localLowerRamificationGroup_of_nonpos K L 0 le_rfl]
  exact hlower

/-- M328.001: lower inertia is the actual supplied residue-action kernel. -/
theorem localLowerRamificationGroup_zero_eq_residue_ker
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    localLowerRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker :=
  (localRamificationZeroResidueKernel K L).1

/-- M328.002: upper inertia is the actual supplied residue-action kernel. -/
theorem localUpperRamificationGroup_zero_eq_residue_ker
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    localUpperRamificationGroup K L 0 =
      (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker :=
  (localRamificationZeroResidueKernel K L).2

end Langlands.NYLL.RamificationTheory.LocalField
