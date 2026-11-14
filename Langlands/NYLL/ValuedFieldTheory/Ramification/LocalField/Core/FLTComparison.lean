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

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.RestrictionStatement
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.EvaluationProof
import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi

noncomputable section

namespace Langlands.NYLL.PortInternal.FltBridge

open Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
open Langlands.NYLL.RamificationTheory.DiscreteValuationField
open Langlands.NYLL.LocalFieldTheory
open scoped BigOperators

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]
variable (huniq : DVF.HasUniqueValuationExtension.{u, v, w, x, x} base target)

def valuationAutHom : Gal(L/K) →* RingAut target.valuationSubring where
  toFun := valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq
  map_one' := by ext a; rfl
  map_mul' σ τ := by
    ext a
    rfl

abbrev valuationAction : MulSemiringAction Gal(L/K) target.valuationSubring :=
  MulSemiringAction.compHom _ (valuationAutHom huniq)

theorem lower_nat_eq (n : ℕ) :
    letI := valuationAction huniq
    lowerRamificationGroup (base := base) (target := target) huniq (n : ℝ) =
      IsLocalRing.lowerRamificationGroup target.valuationSubring Gal(L/K) n := by
  let := valuationAction huniq
  ext σ
  exact mem_lowerRamificationGroup_nat_iff huniq n σ

theorem action_faithful :
    letI := valuationAction huniq
    FaithfulSMul Gal(L/K) target.valuationSubring := by
  let := valuationAction huniq
  let : IsFractionRing target.valuationSubring L :=
    inferInstanceAs (IsFractionRing target.valuation.valuationSubring L)
  refine ⟨fun {σ τ} h => ?_⟩
  have heq : σ.toRingHom = τ.toRingHom :=
    IsFractionRing.ringHom_ext (A := target.valuationSubring) (fun a =>
      congrArg (fun b : target.valuationSubring => (b : L)) (h a))
  exact AlgEquiv.ext fun a => RingHom.congr_fun heq a

theorem herbrand_rat (q : ℚ) :
    letI := valuationAction huniq
    herbrandFunctionOfUniqueExtension (base := base) (target := target) huniq (q : ℝ) =
      (IsLocalRing.herbrandPhi target.valuationSubring Gal(L/K) q : ℝ) := by
  let := valuationAction huniq
  change AntitoneNormalSubgroupFiltration.herbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension huniq) (q : ℝ) = _
  by_cases hq : q ≤ 0
  · rw [AntitoneNormalSubgroupFiltration.herbrandFunction_of_nonpos _ (by exact_mod_cast hq),
      IsLocalRing.herbrandPhi_of_nonpos hq]
  · have hq' : 0 < q := lt_of_not_ge hq
    rw [AntitoneNormalSubgroupFiltration.herbrandFunction_of_floor _
        (by exact_mod_cast hq'.le) ⌊q⌋₊
        (Langlands.Ramification.HerbrandBridge.natFloor_ratCast q),
      IsLocalRing.herbrandPhi_of_pos hq']
    unfold AntitoneNormalSubgroupFiltration.herbrandValueNat
      AntitoneNormalSubgroupFiltration.herbrandSlope
    have hcard (n : ℕ) :
        Nat.card ((lowerRamificationFiltrationOfUniqueExtension huniq).lower n) =
          IsLocalRing.lowerRamificationCard target.valuationSubring Gal(L/K) n := by
      change Nat.card (lowerRamificationGroup huniq (n : ℝ)) =
        Nat.card (IsLocalRing.lowerRamificationGroup target.valuationSubring Gal(L/K) n)
      rw [lower_nat_eq huniq]
    simp only [hcard]
    push_cast
    rw [Langlands.Ramification.HerbrandBridge.sum_Icc_one_eq_sum_range]
    rw [← Finset.sum_div, ← mul_div_assoc, ← add_div]

theorem lower_real_eq (s : ℝ) (hs : 0 ≤ s) :
    letI := valuationAction huniq
    lowerRamificationGroup (base := base) (target := target) huniq s =
      IsLocalRing.lowerRamificationGroup target.valuationSubring Gal(L/K) ⌈s⌉₊ := by
  let := valuationAction huniq
  have hexp : realRamificationExponent s = ⌈s⌉₊ + 1 := by
    unfold realRamificationExponent
    rw [Int.ceil_add_one, Int.toNat_add (Int.ceil_nonneg hs) (by omega)]
    rw [Int.toNat_one, Int.ceil_toNat]
  ext σ
  change (∀ a, valuationSubringAutOfUniqueExtension huniq σ a - a ∈
      target.maximalIdeal ^ realRamificationExponent s) ↔
    (∀ a, valuationSubringAutOfUniqueExtension huniq σ a - a ∈
      target.maximalIdeal ^ (⌈s⌉₊ + 1))
  rw [hexp]

theorem upper_rat_eq [FiniteDimensional K L] (q : ℚ) (hq : 0 ≤ q) :
    letI := valuationAction huniq
    upperRamificationGroupOfUniqueExtension huniq (q : ℝ) =
      IsLocalRing.upperRamificationGroup target.valuationSubring Gal(L/K) q := by
  let := valuationAction huniq
  have hpsi : inverseHerbrandFunctionOfUniqueExtension huniq (q : ℝ) =
      (IsLocalRing.herbrandPsi target.valuationSubring Gal(L/K) q : ℝ) := by
    apply (herbrandFunctionOfUniqueExtension_strictMono huniq).injective
    rw [herbrandFunctionOfUniqueExtension_psi, herbrand_rat,
      IsLocalRing.herbrandPhi_herbrandPsi]
  change lowerRamificationGroup huniq
    (inverseHerbrandFunctionOfUniqueExtension huniq (q : ℝ)) = _
  rw [hpsi,
    lower_real_eq huniq _ (by exact_mod_cast IsLocalRing.herbrandPsi_nonneg hq),
    IsLocalRing.upperRamificationGroup_eq_ceil_herbrandPsi]
  congr 1
  rw [← Int.ceil_toNat, Rat.ceil_cast, Int.ceil_toNat]

theorem phi_zero : herbrandFunctionOfUniqueExtension huniq 0 = 0 :=
  AntitoneNormalSubgroupFiltration.herbrandFunction_zero _

theorem psi_nonneg [FiniteDimensional K L] {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ inverseHerbrandFunctionOfUniqueExtension huniq t := by
  rw [← (herbrandFunctionOfUniqueExtension_strictMono huniq).le_iff_le,
    herbrandFunctionOfUniqueExtension_psi, phi_zero]
  exact ht

theorem upper_eq_lower_ceil [FiniteDimensional K L] {t : ℝ} (ht : 0 ≤ t) :
    upperRamificationGroupOfUniqueExtension huniq t =
      lowerRamificationGroup huniq
        (⌈inverseHerbrandFunctionOfUniqueExtension huniq t⌉₊ : ℝ) := by
  let := valuationAction huniq
  exact (lower_real_eq huniq _ (psi_nonneg huniq ht)).trans (lower_nat_eq huniq _).symm

theorem exists_rat_upper_const [FiniteDimensional K L] {t : ℝ} (ht : 0 ≤ t) :
    ∃ q : ℚ, 0 ≤ q ∧ t ≤ q ∧ ∀ s : ℝ, t ≤ s → s ≤ q →
      upperRamificationGroupOfUniqueExtension huniq s =
        upperRamificationGroupOfUniqueExtension huniq t := by
  let := valuationAction huniq
  let n := ⌈inverseHerbrandFunctionOfUniqueExtension huniq t⌉₊
  let q := IsLocalRing.herbrandPhi target.valuationSubring Gal(L/K) (n : ℚ)
  have hq : herbrandFunctionOfUniqueExtension huniq (n : ℝ) = (q : ℝ) := by
    simpa only [Rat.cast_natCast] using herbrand_rat huniq (n : ℚ)
  have hq0 : (0 : ℝ) ≤ q := by
    rw [← hq, ← phi_zero huniq]
    exact (herbrandFunctionOfUniqueExtension_strictMono huniq).monotone (Nat.cast_nonneg n)
  have htq : t ≤ (q : ℝ) := by
    rw [← hq, ← herbrandFunctionOfUniqueExtension_psi huniq t]
    exact (herbrandFunctionOfUniqueExtension_strictMono huniq).monotone (Nat.le_ceil _)
  refine ⟨q, by exact_mod_cast hq0, htq, ?_⟩
  intro s hts hsq
  rw [upper_eq_lower_ceil huniq (ht.trans hts), upper_eq_lower_ceil huniq ht]
  congr 1
  norm_cast
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    rw [← (herbrandFunctionOfUniqueExtension_strictMono huniq).le_iff_le,
      herbrandFunctionOfUniqueExtension_psi, hq]
    exact hsq
  · exact Nat.ceil_mono ((inverseHerbrandFunctionOfUniqueExtension_strictMono huniq).monotone hts)

section Equivariant

variable {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  {G G' : Type*} [Group G] [Group G'] [MulSemiringAction G A] [MulSemiringAction G' B]

open Langlands.Ramification.HerbrandBridge

theorem phi_of_equivariant (e : A ≃+* B) (f : G ≃* G')
    (he : ∀ (g : G) (a : A), e (g • a) = f g • e a) (q : ℚ) :
    IsLocalRing.herbrandPhi A G q = IsLocalRing.herbrandPhi B G' q := by
  by_cases hq : q ≤ 0
  · rw [IsLocalRing.herbrandPhi_of_nonpos hq, IsLocalRing.herbrandPhi_of_nonpos hq]
  · rw [IsLocalRing.herbrandPhi_of_pos (lt_of_not_ge hq),
      IsLocalRing.herbrandPhi_of_pos (lt_of_not_ge hq)]
    simp_rw [lowerRamificationCard_of_equivariant e f he]

theorem psi_of_equivariant [Finite G] [Finite G'] (e : A ≃+* B) (f : G ≃* G')
    (he : ∀ (g : G) (a : A), e (g • a) = f g • e a) (q : ℚ) :
    IsLocalRing.herbrandPsi A G q = IsLocalRing.herbrandPsi B G' q := by
  apply (IsLocalRing.herbrandPhi_strictMono (R := B) (G := G')).injective
  rw [← phi_of_equivariant e f he, IsLocalRing.herbrandPhi_herbrandPsi,
    IsLocalRing.herbrandPhi_herbrandPsi]

theorem upper_of_equivariant [Finite G] [Finite G'] (e : A ≃+* B) (f : G ≃* G')
    (he : ∀ (g : G) (a : A), e (g • a) = f g • e a) (q : ℚ) :
    (IsLocalRing.upperRamificationGroup A G q).map (f : G →* G') =
      IsLocalRing.upperRamificationGroup B G' q := by
  rw [IsLocalRing.upperRamificationGroup_eq_ceil_herbrandPsi,
    IsLocalRing.upperRamificationGroup_eq_ceil_herbrandPsi,
    psi_of_equivariant e f he]
  exact map_lowerRamificationGroup_of_equivariant e f he _

end Equivariant

end Langlands.NYLL.PortInternal.FltBridge
