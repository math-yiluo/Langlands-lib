import Langlands.Global.RankinSelberg.RealAscendingParabolicQuotient
import Langlands.Global.RankinSelberg.RealParabolicLongestCell
import Langlands.Global.RankinSelberg.RealParabolicTraceProduct
import Langlands.Global.RankinSelberg.RealWhittakerOrbitPositivity

/-! # The nonzero scalar in the real compact parabolic trace -/

noncomputable section

open Set TopologicalSpace
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Whittaker (standardCharacter)
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open RealBlockPosition RealJacquetFrobenius RealPrincipalSeriesDistribution
open RealExactWhittakerUniqueness RealStandardCompactBanach
open RealStrictCharacterLanglandsQuotient (IsCharacterList realStandardModule_eq)
open RealPrincipalSeriesWhittakerUniqueness
open Langlands.Shahidi (swapRank intertwiningUnipotent)

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

local notation "G" => fun d => Langlands.GeneralLinear d ℝ
local notation "U" => fun d => Langlands.GeneralLinear.upperUnipotent d ℝ
local notation "S" => realStandardModule
local notation "W" => fun d => weylLong d ℝ
local notation:max "R" d:max ds:max => representation (n := d) ds
local notation:max "D" d:max ds:max => DerivativeSmoothVectors (matrixModel ℝ d) (R d ds)
local notation:max "act" d:max ds:max => DerivativeSmoothVectors.representation (matrixModel ℝ d) (R d ds)
local notation "X" => fun m p => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => fun m p => 𝓓((⊤ : Opens (X m p)), ℂ)

private theorem whittaker_mul {r : ℕ} (a : ℝˣ) (u v : U (r + 1)) :
    realWhittakerCharacter a (u * v).val = realWhittakerCharacter a u.val * realWhittakerCharacter a v.val :=
  congrArg Units.val ((standardCharacter (realScaledCharacter a) r).map_mul u v)

private theorem whittaker_one {r : ℕ} (a : ℝˣ) : realWhittakerCharacter a (1 : U (r + 1)).val = 1 :=
  congrArg Units.val ((standardCharacter (realScaledCharacter a) r).map_one)

private def characterSeriesEquiv (r : ℕ) (ds : List RealBlock) (hds : IsCharacterList ds) :
    principalSeries ℝ (r + 1) (posChar (shiftedExponent (r + 1) ds) (positionSign (r + 1) ds)) ≃ₗ[ℂ]
      S (r + 1) ds :=
  LinearEquiv.ofEq _ _ ((principalSeries_posChar_shiftedExponent _ _).trans (realStandardModule_eq hds).symm)

set_option maxHeartbeats 650000 in
private theorem evaluation_ne_zero_of_phasedSection {r : ℕ} (ds : List RealBlock) (hds : IsCharacterList ds)
    (a : ℝˣ) (L : D (r + 1) ds →L[ℂ] ℂ) (hL : IsSmoothWhittakerEvaluation ds a L) (hLne : L ≠ 0)
    (F : S (r + 1) ds) (hF : tsupport F.val ⊆ Units.val ⁻¹' (longestBruhatCell ℝ r : Set _))
    (hPhase : ∀ u : U (r + 1), 0 ≤ (realWhittakerCharacter a u.val * F.val (W (r + 1) * (u⁻¹).val)).re)
    (hPos : 0 < (F.val (W (r + 1))).re) : L (derivativeEquiv ds F) ≠ 0 := by
  let s := shiftedExponent (r + 1) ds
  let e := positionSign (r + 1) ds
  let E := characterSeriesEquiv r ds hds
  let J := E.trans (derivativeEquiv ds)
  let ℓ := L.toLinearMap.comp J.toLinearMap
  have hBound : RealPrincipalSeries.HasCompactDerivativeBound r (normalizedCharacterBlocks s e) ℓ := by
    obtain ⟨k, Xs, c, hc, hB⟩ := has_compact_bound_of_continuous ds L
    exact ⟨k, Xs, c, hc, fun f b hb => hB (E f) b hb⟩
  have hCov : IsWhittakerFunctional s e a ℓ := by
    intro u f
    have he : E (RealPrincipalSeries.translate r (normalizedCharacterBlocks s e) u.val f) =
        RealStandardCompactBanach.translate ds u.val (E f) := Subtype.ext rfl
    change L (derivativeEquiv ds (E (RealPrincipalSeries.translate r
      (normalizedCharacterBlocks s e) u.val f))) = realWhittakerCharacter a u.val * L (derivativeEquiv ds (E f))
    rw [he, derivativeEquiv_translate]
    exact hL u _
  have hne : ℓ ≠ 0 := by
    intro h0
    apply hLne
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨f, rfl⟩ := J.surjective v
    exact LinearMap.congr_fun h0 f
  have h := realWhittakerOrbitPositivity s e a ℓ hBound hCov hne (E.symm F) hF hPhase hPos
  change L (derivativeEquiv ds (E (E.symm F))) ≠ 0 at h
  simpa only [LinearEquiv.apply_symm_apply] using h

private theorem exists_phasedTest {m p : ℕ} (a : ℝˣ) :
    ∃ (φ : Test m p) (κ : X m p → ℝ), (∀ Y, 0 ≤ κ Y) ∧ κ 0 = 1 ∧
      ∀ Y, φ Y = transversePhase a Y * (κ Y : ℂ) := by
  let b : ContDiffBump (0 : X m p) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f (Y : X m p) : ℂ := transversePhase a Y * (b Y : ℂ)
  exact ⟨⟨f, (contDiff_transversePhase a).mul (Complex.ofRealCLM.contDiff.comp b.contDiff),
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left, subset_univ _⟩,
    b, fun _ => b.nonneg, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), fun _ => rfl⟩

private theorem exists_phased_blockUpper {m p : ℕ} (a : ℝˣ) (v : U (p + 1 + m + 1)) :
    ∃ (A : U (m + 1)) (B : U (p + 1)) (Y : X m p),
      v.val = swapRank (p + 1) (m + 1) ℝ (blockSum (A.val, B.val) * Shahidi.upper (m + 1) (p + 1) ℝ Y) ∧
      realWhittakerCharacter a v.val =
        realWhittakerCharacter a A.val * realWhittakerCharacter a B.val * transversePhase a Y := by
  obtain ⟨B, A, Y, hv⟩ := Langlands.Whittaker.upperUnipotent_exchanged_factorization
    (Nat.succ_pos p) (Nat.succ_pos m) v
  let diag : U (p + 1 + m + 1) := ⟨swapRank (p + 1) (m + 1) ℝ (blockSum (A.val, B.val)),
    Shahidi.swapRank_mem_upperUnipotent _ _ ℝ (Langlands.Whittaker.blockSum_mem_upperUnipotent A B)⟩
  let radical : U (p + 1 + m + 1) := ⟨intertwiningUnipotent (p + 1) (m + 1) ℝ Y,
    Shahidi.intertwiningUnipotent_mem_upperUnipotent _ _ ℝ Y⟩
  have hdiag : realWhittakerCharacter a diag.val =
      realWhittakerCharacter a A.val * realWhittakerCharacter a B.val :=
    (Langlands.Whittaker.standardCharacter_exchanged_blockSum (realScaledCharacter a) B A).trans (mul_comm _ _)
  have hrad : realWhittakerCharacter a radical.val = transversePhase a Y :=
    whittakerCharacter_intertwiningUnipotent a Y
  refine ⟨A, B, Y, ?_, ?_⟩
  · simpa only [map_mul, intertwiningUnipotent] using hv
  · have h : v = diag * radical := Subtype.ext hv
    rw [h, whittaker_mul, hdiag, hrad]

set_option maxHeartbeats 900000 in
private theorem detects_characterLists {m p : ℕ} (d₁ d₂ : List RealBlock)
    (h₁ : IsCharacterList d₁) (h₂ : IsCharacterList d₂) : HasParabolicTraceDetection m p d₁ d₂ := by
  intro hm hp a L hL hne
  obtain ⟨F, κ₁, _, hκ₁, hκ₁one, hFO, hF⟩ := RealLongestCellSection.realLongestCellSection m
    (shiftedExponent (m + 1) d₁) (positionSign (m + 1) d₁) a
  obtain ⟨H, κ₂, _, hκ₂, hκ₂one, hHO, hH⟩ := RealLongestCellSection.realLongestCellSection p
    (shiftedExponent (p + 1) d₂) (positionSign (p + 1) d₂) a
  obtain ⟨φ, κ₀, hκ₀, hκ₀one, hφ⟩ := exists_phasedTest (m := m) (p := p) a
  let f := characterSeriesEquiv m d₁ h₁ F
  let g := characterSeriesEquiv p d₂ h₂ H
  let Q := standardSection f.val g.val φ
  have hGeometry := realParabolicLongestCell m p f.val g.val φ f.2.1.1 g.2.1.1 φ.contDiff φ.hasCompactSupport
  have hPhase (v : U (p + 1 + m + 1)) : ∃ b : ℝ, 0 ≤ b ∧
      Q (W (p + 1 + m + 1) * v.val) = realWhittakerCharacter a v.val * (b : ℂ) := by
    obtain ⟨A, B, Y, hv, hψ⟩ := exists_phased_blockUpper a v
    have hF' : f.val (W (m + 1) * A.val) = realWhittakerCharacter a A.val * (κ₁ A : ℂ) := hF A
    have hH' : g.val (W (p + 1) * B.val) = realWhittakerCharacter a B.val * (κ₂ B : ℂ) := hH B
    refine ⟨κ₁ A * κ₂ B * κ₀ Y, mul_nonneg (mul_nonneg (hκ₁ A) (hκ₂ B)) (hκ₀ Y), ?_⟩
    calc
      Q (W (p + 1 + m + 1) * v.val) = f.val (W (m + 1) * A.val) * g.val (W (p + 1) * B.val) * φ Y := by
        rw [hv]
        exact hGeometry.2 A B Y
      _ = _ := by rw [hF', hH', hφ, hψ, Complex.ofReal_mul, Complex.ofReal_mul]; ring
  have hPositive (u : U (p + 1 + m + 1)) :
      0 ≤ (realWhittakerCharacter a u.val * Q (W (p + 1 + m + 1) * (u⁻¹).val)).re := by
    obtain ⟨b, hb, he⟩ := hPhase u⁻¹
    have hc := (whittaker_mul a u u⁻¹).symm
    rw [mul_inv_cancel, whittaker_one] at hc
    rw [he, ← mul_assoc, hc, one_mul, Complex.ofReal_re]
    exact hb
  have hW : Q (W (p + 1 + m + 1)) = 1 := by
    have he := hGeometry.2 (1 : U (m + 1)) (1 : U (p + 1)) 0
    have h₀ : blockSum ((1 : G (m + 1)), (1 : G (p + 1))) = 1 := map_one blockSum
    simp only [Subgroup.coe_one, h₀, Shahidi.upper_zero, mul_one, map_one] at he
    have h₁' := hF (1 : U (m + 1))
    have h₂' := hH (1 : U (p + 1))
    change f.val (W (m + 1) * (1 : U (m + 1)).val) = _ at h₁'
    change g.val (W (p + 1) * (1 : U (p + 1)).val) = _ at h₂'
    have hOne₁ : realWhittakerCharacter a (1 : G (m + 1)) = 1 := whittaker_one a
    have hOne₂ : realWhittakerCharacter a (1 : G (p + 1)) = 1 := whittaker_one a
    simp only [Subgroup.coe_one, mul_one, hκ₁one, hκ₂one, Complex.ofReal_one, hOne₁, hOne₂] at h₁' h₂'
    change standardSection f.val g.val φ (W (p + 1 + m + 1)) = 1
    rw [he, h₁', h₂', hφ, hκ₀one, transversePhase_zero, Complex.ofReal_one]
    simp only [one_mul]
  let v := smoothSectionVector hm hp f g φ
  let V := (derivativeEquiv (d₂ ++ d₁)).symm v
  have hV : V.val = Q := by
    funext x
    have h := reconstruct_translate_smoothSectionVector hm hp f g φ 1 x
    simpa only [map_one, Module.End.one_apply, mul_one] using h
  have hChar : IsCharacterList (d₂ ++ d₁) := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact h₂ b hb
    · exact h₁ b hb
  refine ⟨f, g, φ, ?_⟩
  have hv : L (derivativeEquiv (d₂ ++ d₁) V) ≠ 0 := evaluation_ne_zero_of_phasedSection
    (d₂ ++ d₁) hChar a L hL hne V (by rw [hV]; exact hGeometry.1 hFO hHO)
    (by rw [hV]; exact hPositive) (by rw [hV, hW, Complex.one_re]; exact zero_lt_one)
  simpa only [V, LinearEquiv.apply_symm_apply] using hv

/-- Every nonzero real Whittaker evaluation is detected by a compact parabolic section. -/
theorem realParabolicTraceDetection (m p : ℕ) (d₁ d₂ : List RealBlock) :
    HasParabolicTraceDetection m p d₁ d₂ :=
  hasParabolicTraceDetection_of_characters detects_characterLists

/-- The compact trace against two nonzero Levi evaluations has a nonzero comparison scalar
for every nonzero ambient evaluation. -/
def RealParabolicTraceNonzeroStatement : Prop :=
  ∀ (m p : ℕ) (d₁ d₂ : List RealBlock) (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1)
    (a : ℝˣ) (L : D (p + 1 + m + 1) (d₂ ++ d₁) →L[ℂ] ℂ)
    (L₁ : D (m + 1) d₁ →L[ℂ] ℂ) (L₂ : D (p + 1) d₂ →L[ℂ] ℂ),
    IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L →
    IsSmoothWhittakerEvaluation d₁ a L₁ → IsSmoothWhittakerEvaluation d₂ a L₂ →
    L ≠ 0 → L₁ ≠ 0 → L₂ ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (f : S (m + 1) d₁) (g : S (p + 1) d₂) (φ : Test m p),
        L (smoothSectionVector hm hp f g φ) = c * L₁ (derivativeEquiv d₁ f) *
          L₂ (derivativeEquiv d₂ g) * transverseMoment a φ

theorem realParabolicTraceNonzero : RealParabolicTraceNonzeroStatement := by
  intro m p d₁ d₂ hm hp a L L₁ L₂ hL hL₁ hL₂ hLne hL₁ne hL₂ne
  obtain ⟨c, hc⟩ := realParabolicTraceProduct m p d₁ d₂ hm hp a L L₁ L₂ hL hL₁ hL₂ hL₁ne hL₂ne
  obtain ⟨f, g, φ, h⟩ := realParabolicTraceDetection m p d₁ d₂ hm hp a L hL hLne
  refine ⟨c, ?_, hc⟩
  intro hzero
  exact h (by simp only [hc, hzero, zero_mul])

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
