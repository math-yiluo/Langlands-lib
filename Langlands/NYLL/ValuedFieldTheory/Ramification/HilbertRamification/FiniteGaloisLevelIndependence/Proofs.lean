/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 296, 2026-11-13: isolate M307.002–.006 from pinned
commit fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces,
prove the closed proposition targets using focused published imports,
and reuse Mathlib local-ring maximal-ideal transport directly.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevelIndependence.Statements
import Mathlib.RingTheory.LocalRing.RingHom.Basic

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

open Langlands.NYLL.ValuationTheory
open Langlands.NYLL.ValuationTheory.DiscreteValuationField

private theorem lowerRamificationFiltration_ext
    {G : Type*} [Group G]
    {F F' :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration G}
    (h : F.lower = F'.lower) :
    F = F' := by
  cases F
  cases F'
  cases h
  rfl

theorem lowerRamificationGroup_eq_of_valuationSubring_eq :
    lowerRamificationGroup_eq_of_valuationSubring_eqStatement := by
  intro K L _ _ _ base target target' _ _ huniq huniq' hvaluationSubring s
  let e : target.valuationSubring ≃+* target'.valuationSubring :=
    { toFun := fun a => ⟨(a : L), by
        rw [← hvaluationSubring]
        exact a.property⟩
      invFun := fun a => ⟨(a : L), by
        rw [hvaluationSubring]
        exact a.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        rfl
      map_add' := by
        intro a b
        apply Subtype.ext
        rfl }
  have hmap :
      Ideal.map
          (e : target.valuationSubring →+* target'.valuationSubring)
          target.maximalIdeal =
        target'.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have hmap_real :
      Ideal.map
          (e : target.valuationSubring →+* target'.valuationSubring)
          (realRamificationIdeal target s) =
        realRamificationIdeal target' s := by
    simp only [realRamificationIdeal, Ideal.map_pow, hmap]
  have he_aut (σ : Gal(L/K)) (a : target.valuationSubring) :
      e (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a) =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target') huniq' σ (e a) := by
    ext
    rfl
  ext σ
  rw [mem_lowerRamificationGroup_iff, mem_lowerRamificationGroup_iff]
  constructor
  · intro hσ a'
    obtain ⟨a, rfl⟩ := e.surjective a'
    have ha := hσ a
    have hemap :
        e (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) ∈
          Ideal.map
            (e : target.valuationSubring →+* target'.valuationSubring)
            (realRamificationIdeal target s) :=
      Ideal.mem_map_of_mem _ ha
    rw [hmap_real] at hemap
    simpa only [map_sub, he_aut] using hemap
  · intro hσ a
    have ha' := hσ (e a)
    have hemap :
        e (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) ∈
          realRamificationIdeal target' s := by
      simpa only [map_sub, he_aut] using ha'
    rw [← hmap_real] at hemap
    rcases (Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target'.valuationSubring)
      e.surjective).1 hemap with ⟨b, hb, hbe⟩
    have hba :
        b = valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a :=
      e.injective hbe
    simpa only [hba] using hb

theorem lowerRamificationFiltration_eq_of_valuationSubring_eq :
    lowerRamificationFiltration_eq_of_valuationSubring_eqStatement := by
  intro K L _ _ _ base target target' _ _ huniq huniq' hvaluationSubring
  apply lowerRamificationFiltration_ext
  funext n
  exact lowerRamificationGroup_eq_of_valuationSubring_eq
    huniq huniq' hvaluationSubring (n : ℝ)

theorem herbrandFunction_eq_of_valuationSubring_eq :
    herbrandFunction_eq_of_valuationSubring_eqStatement := by
  intro K L _ _ _ base target target' _ _ _ huniq huniq' hvaluationSubring
  have hF :=
    lowerRamificationFiltration_eq_of_valuationSubring_eq
      huniq huniq' hvaluationSubring
  exact congrArg
    (fun F =>
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction F)
    hF

theorem inverseHerbrandFunction_eq_of_valuationSubring_eq :
    inverseHerbrandFunction_eq_of_valuationSubring_eqStatement := by
  intro K L _ _ _ base target target' _ _ _ huniq huniq' hvaluationSubring
  have hF :=
    lowerRamificationFiltration_eq_of_valuationSubring_eq
      huniq huniq' hvaluationSubring
  exact congrArg
    (fun F =>
      DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction F)
    hF

theorem upperRamificationGroup_eq_of_valuationSubring_eq :
    upperRamificationGroup_eq_of_valuationSubring_eqStatement := by
  intro K L _ _ _ base target target' _ _ _ huniq huniq' hvaluationSubring t
  change lowerRamificationGroup (base := base) (target := target) huniq
      (inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq t) =
    lowerRamificationGroup (base := base) (target := target') huniq'
      (inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target') huniq' t)
  rw [inverseHerbrandFunction_eq_of_valuationSubring_eq
    huniq huniq' hvaluationSubring]
  exact lowerRamificationGroup_eq_of_valuationSubring_eq
    huniq huniq' hvaluationSubring _

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
