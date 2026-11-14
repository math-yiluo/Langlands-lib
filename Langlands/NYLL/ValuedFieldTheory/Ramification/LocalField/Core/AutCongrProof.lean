/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 296, 2026-11-13: adapt M327.006 at pinned commit
fbd320cd8b1b06487c58227e92eb135794267709 to its published closed target.
Use chosen-valuation uniqueness directly on a comapped valuation to obtain
an equivalence of the chosen valuation rings, avoiding a pulled DVF and
the source's valuation-ring independence detour. Reuse Mathlib maximal-
ideal transport and published Herbrand laws. Prefix namespaces and use
focused imports; all extension witnesses are local.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.AutCongrStatement
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.EvaluationProof
import Mathlib.RingTheory.LocalRing.RingHom.Basic

noncomputable section

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- A base-linear equivalence transports the actual local upper groups. -/
theorem localUpperRamificationGroup_map_autCongr :
    localUpperRamificationGroup_map_autCongrStatement := by
  intro K L M _ _ _ _ _ _ _ _ _ _ _ _ e t
  let base := localCompleteDVF K
  let targetL := chosenLocalExtensionCompleteDVF K L
  let targetM := chosenLocalExtensionCompleteDVF K M
  let hExtL : base.valuation.HasExtension targetL.valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  let hExtM : base.valuation.HasExtension targetM.valuation :=
    Classical.choose (chosenLocalExtension_properties K M)
  let pulledVal := targetM.valuation.comap e.toRingHom
  let hExtPulled : base.valuation.HasExtension pulledVal :=
    { val_isEquiv_comap := by
        rw [_root_.Valuation.isEquiv_iff_val_le_one]
        intro a
        change base.valuation a ≤ 1 ↔ targetM.valuation (e (algebraMap K L a)) ≤ 1
        rw [e.commutes]
        exact (_root_.Valuation.HasExtension.val_map_le_one_iff
          (vR := base.valuation) (vA := targetM.valuation) a).symm }
  let huniqL :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetL.toDVF :=
    chosenLocalExtension_uniqueValuationExtension.{0} K L
  let huniqM :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base.toDVF targetM.toDVF :=
    chosenLocalExtension_uniqueValuationExtension.{0} K M
  have hRing : targetL.valuation.valuationSubring = pulledVal.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring _ _).mp (huniqL pulledVal)
  let r : targetL.valuationSubring ≃+* targetM.valuationSubring :=
    (RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hRing)).trans
      (Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.valuationSubringRingEquivOfComap
        targetM.valuation e.toRingEquiv)
  let φ : Gal(L/K) ≃* Gal(M/K) := AlgEquiv.autCongr e
  have hmapMaximalIdeal :
      Ideal.map
          (r : targetL.valuationSubring →+* targetM.valuationSubring)
          (IsLocalRing.maximalIdeal targetL.valuationSubring) =
        IsLocalRing.maximalIdeal targetM.valuationSubring :=
    IsLocalRing.map_ringEquiv_maximalIdeal r
  have hmapIdeal (s : ℝ) :
      Ideal.map (r : targetL.valuationSubring →+* targetM.valuationSubring)
          (realRamificationIdeal targetL.toDVF s) =
        realRamificationIdeal targetM.toDVF s := by
    unfold realRamificationIdeal
    rw [Ideal.map_pow, hmapMaximalIdeal]
  have hideal (s : ℝ) (x : targetL.valuationSubring) :
      x ∈ realRamificationIdeal targetL.toDVF s ↔
        r x ∈ realRamificationIdeal targetM.toDVF s := by
    constructor
    · intro hx
      have hrx :
          r x ∈ Ideal.map
            (r : targetL.valuationSubring →+* targetM.valuationSubring)
            (realRamificationIdeal targetL.toDVF s) :=
        Ideal.mem_map_of_mem
          (r : targetL.valuationSubring →+* targetM.valuationSubring) hx
      simpa only [hmapIdeal s] using hrx
    · intro hrx
      have hrx' :
          r x ∈ Ideal.map
            (r : targetL.valuationSubring →+* targetM.valuationSubring)
            (realRamificationIdeal targetL.toDVF s) := by
        simpa only [hmapIdeal s] using hrx
      exact Ideal.apply_mem_of_equiv_iff.mp hrx'
  have hdisplacement (σ : Gal(L/K)) (a : targetL.valuationSubring) :
      r (valuationSubringAutOfUniqueExtension
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL σ a - a) =
        valuationSubringAutOfUniqueExtension
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM (φ σ) (r a) - r a := by
    apply Subtype.ext
    change
      e (σ (a : L) - (a : L)) =
        (AlgEquiv.autCongr e σ) (e (a : L)) - e (a : L)
    simp [AlgEquiv.autCongr_apply]
  have hmem (s : ℝ) (σ : Gal(L/K)) :
      σ ∈ lowerRamificationGroup
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL s ↔
        φ σ ∈ lowerRamificationGroup
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM s := by
    constructor
    · intro hσ a
      let b : targetL.valuationSubring := r.symm a
      have hb := (hideal s
        (valuationSubringAutOfUniqueExtension
              (base := base.toDVF) (target := targetL.toDVF)
              huniqL σ b - b)).1 (hσ b)
      rw [hdisplacement σ b] at hb
      simpa [b] using hb
    · intro hσ a
      have ha := hσ (r a)
      rw [← hdisplacement σ a] at ha
      exact (hideal s _).2 ha
  have hlower (s : ℝ) :
      Subgroup.map φ.toMonoidHom
          (lowerRamificationGroup
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL s) =
        lowerRamificationGroup
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM s := by
    ext τ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (hmem s σ).1 hσ
    · intro hτ
      refine ⟨φ.symm τ, (hmem s (φ.symm τ)).2 ?_, φ.apply_symm_apply τ⟩
      simpa using hτ
  have hcard (n : ℕ) :
      Nat.card
          ((lowerRamificationFiltrationOfUniqueExtension
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL).lower n) =
        Nat.card
          ((lowerRamificationFiltrationOfUniqueExtension
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM).lower n) := by
    let H :=
      lowerRamificationGroup
        (base := base.toDVF) (target := targetL.toDVF)
        huniqL (n : ℝ)
    let q :=
      (φ.subgroupMap H).trans
        (MulEquiv.subgroupCongr (hlower (n : ℝ)))
    exact Nat.card_congr q.toEquiv
  have hherbrand (s : ℝ) :
      herbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetL.toDVF)
          huniqL s =
        herbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM s := by
    exact
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_eq_of_card_lower_eq
        _ _ hcard s
  have hinverse (u : ℝ) :
      inverseHerbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetL.toDVF)
          huniqL u =
        inverseHerbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM u := by
    apply
      (herbrandFunctionOfUniqueExtension_strictMono
        (base := base.toDVF) (target := targetM.toDVF)
        huniqM).injective
    rw [herbrandFunctionOfUniqueExtension_psi]
    rw [← hherbrand]
    rw [herbrandFunctionOfUniqueExtension_psi]
  have hpulled :
      Subgroup.map φ.toMonoidHom
          (upperRamificationGroupOfUniqueExtension
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL t) =
        upperRamificationGroupOfUniqueExtension
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM t := by
    change
      Subgroup.map φ.toMonoidHom
          (lowerRamificationGroup
            (base := base.toDVF) (target := targetL.toDVF)
            huniqL
            (inverseHerbrandFunctionOfUniqueExtension
              (base := base.toDVF) (target := targetL.toDVF)
              huniqL t)) =
        lowerRamificationGroup
          (base := base.toDVF) (target := targetM.toDVF)
          huniqM
          (inverseHerbrandFunctionOfUniqueExtension
            (base := base.toDVF) (target := targetM.toDVF)
            huniqM t)
    rw [hinverse]
    exact hlower _
  change
    Subgroup.map φ.toMonoidHom
        (upperRamificationGroupOfUniqueExtension
          (base := base.toDVF) (target := targetL.toDVF)
          huniqL t) =
      upperRamificationGroupOfUniqueExtension
        (base := base.toDVF) (target := targetM.toDVF)
        huniqM t
  exact hpulled

end Langlands.NYLL.RamificationTheory.LocalField
