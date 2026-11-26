import Langlands.Global.RankinSelberg.RealWhittakerTranslatedIntegrals
import Langlands.Global.RankinSelberg.RealUnequalDualFamily
import Langlands.Global.RankinSelberg.ArchimedeanMellinPair

/-! # Uniform bounds for compact families of right translates of real Whittaker functions -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslatedMellin

open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open ArchimedeanMellinPair (RapidDecay)
open RealIwasawa (alpha continuous_alpha kpart npart npart_mul_torus_mul_kpart alpha_unipotent_mul
  alpha_torus_mul alpha_torus_mul_unitary torus)
open RealConvergenceAnalysis (rootPos)
open RealUnequalFamily (HasLeftCharacter HasUniformGauge hasUniformGauge_of_derivativeGrowth
  ordinary_halfPlaneDomination dual_halfPlaneDomination)
open RealUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos realUnequalIntegrand_eq_mul
  realUnequalDualKernel_eq_mul)
open RealWhittakerTranslatedIntegrals (weightedOrdinary weightedDual)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "R" => fun r t => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ
local notation "ρ" => ArchimedeanLocal.translateFunction

/-- The simple-root gauge bound at an arbitrary group element. -/
def HasGaugeBound {n : ℕ} (W : G (n + 1) → ℂ) : Prop :=
  ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G (n + 1),
    ‖W g‖ ≤ C * Real.exp (-(M : ℝ) * rootPos (alpha g) + (N : ℝ) * ∑ j, |alpha g j|)

/-- Members of the refined real Whittaker space satisfy the simple-root gauge bound. -/
theorem hasGaugeBound_of_mem_model {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    {W : G (r + 1) → ℂ} (hW : W ∈ realUniformWhittakerModel r ds a) : HasGaugeBound W := by
  obtain ⟨hreg, N, hN⟩ := realUniformWhittakerRegularity r ds a W hW
  have hU : HasUniformGauge (Set.univ : Set Unit) (fun _ => W) :=
    hasUniformGauge_of_derivativeGrowth (a := a) Set.univ (fun _ => W) (fun _ _ Xs => hreg Xs)
      (N := N) (fun Xs => by
        obtain ⟨C, hC, hb⟩ := hN Xs
        exact ⟨C, hC, fun _ _ g => hb g⟩)
  have hchar : HasLeftCharacter a W := fun u hu g => (hreg []).1 u hu g
  obtain ⟨N', hN'⟩ := hU.any (fun _ _ u hu g => hchar.norm_eq u hu g)
  refine ⟨N', fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN' M
  exact ⟨C, hC, fun g => hb () (mem_univ _) g⟩

/-- The logarithmic displacement under a right translation is determined by the compact factor. -/
theorem alpha_right_mul {n : ℕ} (x y : G n) :
    alpha (x * y) = alpha x + alpha ((kpart x).val * y) := by
  calc
    _ = alpha ((npart x).val * (torus (alpha x) * ((kpart x).val * y))) := by
      rw [← mul_assoc, ← mul_assoc, npart_mul_torus_mul_kpart]
    _ = _ := by rw [alpha_unipotent_mul, alpha_torus_mul]

private theorem rootPos_le_of_bounded_shift {r : ℕ} (y z : Fin (r + 1) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (h : ∀ i, |z i| ≤ L) : rootPos y ≤ rootPos (y + z) + (r : ℝ) * (2 * L) := by
  unfold rootPos
  calc
    _ ≤ ∑ i : Fin r, (max ((y + z) i.castSucc - (y + z) i.succ) 0 + 2 * L) := by
      refine Finset.sum_le_sum fun i _ => max_le ?_ ?_
      · have hi := (abs_le.mp (h i.castSucc)).1
        have hj := (abs_le.mp (h i.succ)).2
        have hm := le_max_left ((y + z) i.castSucc - (y + z) i.succ) 0
        simp only [Pi.add_apply] at hm ⊢
        linarith
      · exact add_nonneg (le_max_right _ _) (mul_nonneg (by norm_num) hL)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A compact family of right translates of a function with the simple-root gauge bound has a
uniform gauge. -/
theorem compact_rightTranslate_uniformGauge {r : ℕ} {W : G (r + 1) → ℂ} (hW : HasGaugeBound W)
    (S : Set (G (r + 1))) (hS : IsCompact S) :
    HasUniformGauge S (fun s g => W (g * s)) := by
  let U := unitaryCompact ℝ (r + 1)
  let F := fun p : U × G (r + 1) => ∑ i, |alpha (p.1.val * p.2) i|
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp (continuous_alpha.comp
      ((continuous_subtype_val.comp continuous_fst).mul continuous_snd))).abs
  obtain ⟨L₀, hBound⟩ := (isCompact_univ.prod hS).exists_bound_of_continuousOn hF.continuousOn
  let L := max L₀ 0
  have hL : 0 ≤ L := le_max_right _ _
  have hb (k : U) (s : G (r + 1)) (hs : s ∈ S) : (∑ i, |alpha (k.val * s) i|) ≤ L := by
    have hh := hBound (k, s) ⟨mem_univ k, hs⟩
    change ‖∑ i, |alpha (k.val * s) i|‖ ≤ L₀ at hh
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hh
    exact hh.trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hWb⟩ := hN J
  let E : ℝ := (N : ℝ) * L + (J : ℝ) * (r : ℝ) * (2 * L)
  refine ⟨C * Real.exp E, mul_nonneg hC (Real.exp_nonneg _), fun s hs y k => ?_⟩
  let g : G (r + 1) := torus y * (k : G (r + 1))
  have hy : alpha g = y := alpha_torus_mul_unitary y k
  let z := alpha ((kpart g).val * s)
  have hz : (∑ i, |z i|) ≤ L := hb (kpart g) s hs
  have hzi (i : Fin (r + 1)) : |z i| ≤ L :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i)).trans hz
  have hLen : (∑ i, |(y + z) i|) ≤ (∑ i, |y i|) + L := by
    rw [← add_le_add_iff_left (∑ i, |y i|)] at hz
    apply le_trans ?_ hz
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => abs_add_le _ _
  have hRoot := rootPos_le_of_bounded_shift y z L hL hzi
  have hh₁ := mul_le_mul_of_nonneg_left hLen (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hh₂ := mul_le_mul_of_nonneg_left hRoot (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  have hExp : -(J : ℝ) * rootPos (y + z) + (N : ℝ) * (∑ i, |(y + z) i|) ≤
      -(J : ℝ) * rootPos y + (N : ℝ) * (∑ i, |y i|) + E := by
    dsimp only [E]
    nlinarith only [hh₁, hh₂]
  change ‖W (g * s)‖ ≤ _
  refine (hWb (g * s)).trans ?_
  rw [alpha_right_mul, hy]
  change C * Real.exp (-(J : ℝ) * rootPos (y + z) + (N : ℝ) * (∑ i, |(y + z) i|)) ≤ _
  refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) hC).trans_eq ?_
  rw [Real.exp_add]
  ring

private theorem norm_weight_mul_le {δ : ℝ} (hδ : 0 < δ) (f : ℝ → ℂ) {C τ : ℝ}
    (hf : ‖f δ‖ ≤ C * δ ^ τ) (z : ℂ) : ‖z * f δ‖ ≤ C * ‖z * (δ : ℂ) ^ (τ : ℂ)‖ := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hδ, Complex.ofReal_re]
  calc
    _ ≤ ‖z‖ * (C * δ ^ τ) := mul_le_mul_of_nonneg_left hf (norm_nonneg _)
    _ = _ := by ring

/-- Both rapidly weighted kernels for fixed translates have integrable bounds uniform in the
additional compact parameters used in their compact approximations. -/
theorem exists_compact_mellin_bounds {r t : ℕ} (h : t < r) (a : ℝˣ) (D : RealQuotientMeasureData t)
    {W : G (r + 1) → ℂ} {V : G (t + 1) → ℂ} (hWc : HasLeftCharacter a W)
    (hVc : HasLeftCharacter (-a) V) (hWg : HasGaugeBound W) (hVg : HasGaugeBound V)
    (g : G (r + 1)) (g' : G (t + 1))
    (f f' : ℝ → ℂ) (hf : RapidDecay f) (hf' : RapidDecay f') :
    ∃ (M : Q t → ℝ) (M' : Q t × R r t → ℝ),
      Integrable M D.measure ∧ Integrable M' (realUnequalDualMeasure (r := r) a D) ∧
      (∀ q (k : KU (r + 1)) (l : KU (t + 1)),
        ‖weightedOrdinary h (ρ (k.val * g) W) (ρ (l.val * g') V) f q‖ ≤ M q) ∧
      (∀ p (k : KU (r + 1)) (l : KU (t + 1)),
        ‖weightedDual h (ρ (k.val * g) W) (ρ (l.val * g') V) f' p‖ ≤ M' p) := by
  let T := (KU (r + 1) × KU (t + 1)) × ℂ
  let A := fun p : T => ρ (p.1.1.val * g) W
  let B := fun p : T => ρ (p.1.2.val * g') V
  let s : T → ℂ := Prod.snd
  let S₁ := Set.range fun k : KU (r + 1) => k.val * g
  let S₂ := Set.range fun k : KU (t + 1) => k.val * g'
  have hS₁ : IsCompact S₁ := isCompact_range (continuous_subtype_val.mul continuous_const)
  have hS₂ : IsCompact S₂ := isCompact_range (continuous_subtype_val.mul continuous_const)
  have hA (p : T) : HasLeftCharacter a (A p) := by
    intro u hu x
    dsimp only [A, ArchimedeanLocal.translateFunction]
    rw [mul_assoc, hWc u hu]
  have hB (p : T) : HasLeftCharacter (-a) (B p) := by
    intro u hu x
    dsimp only [B, ArchimedeanLocal.translateFunction]
    rw [mul_assoc, hVc u hu]
  have hA₀ : HasUniformGauge Set.univ A := by
    obtain ⟨N, hN⟩ := compact_rightTranslate_uniformGauge hWg S₁ hS₁
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hW⟩ := hN J
    exact ⟨C, hC, fun p _ => hW _ ⟨p.1.1, rfl⟩⟩
  have hB₀ : HasUniformGauge Set.univ B := by
    obtain ⟨N, hN⟩ := compact_rightTranslate_uniformGauge hVg S₂ hS₂
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hV⟩ := hN J
    exact ⟨C, hC, fun p _ => hV _ ⟨p.1.2, rfl⟩⟩
  obtain ⟨σ, hOrd⟩ := ordinary_halfPlaneDomination h D Set.univ A B s hA hB hA₀ hB₀
  obtain ⟨σ', hDual⟩ := dual_halfPlaneDomination h D a Set.univ A B s hA hB hA₀ hB₀
  let τ := σ + 1
  let τ' := σ' + 1
  obtain ⟨N, hN, hNbound⟩ := hOrd τ
  obtain ⟨N', hN', hN'bound⟩ := hDual τ'
  obtain ⟨C, hC⟩ := hf τ
  obtain ⟨C', hC'⟩ := hf' τ'
  have hC₀ := RapidDecay.nonneg_const hC
  have hC'₀ := RapidDecay.nonneg_const hC'
  refine ⟨C • N, C' • N', hN.const_mul C, hN'.const_mul C', ?_, ?_⟩
  · intro q k l
    let p : T := ((k, l), (τ : ℂ))
    have hp : σ < (s p).re := by dsimp [s, p, τ]; linarith
    have hz : (s p).re ≤ τ := by simp [s, p]
    have hb := hNbound p (mem_univ p) hp hz q
    have hc := norm_weight_mul_le (quotientDetAbs_pos q) f (hC _ (quotientDetAbs_pos q))
      (realUnequalIntegrand h (A p) (B p) 0 q)
    rw [← realUnequalIntegrand_eq_mul] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hb hC₀)
  · intro x k l
    let p : T := ((k, l), (τ' : ℂ))
    have hp : σ' < (s p).re := by dsimp [s, p, τ']; linarith
    have hz : (s p).re ≤ τ' := by simp [s, p]
    have hb := hN'bound p (mem_univ p) hp hz x
    have hc := norm_weight_mul_le (quotientDetAbs_pos x.1) f' (hC' _ (quotientDetAbs_pos x.1))
      (realUnequalDualKernel h (A p) (B p) 0 x)
    rw [← realUnequalDualKernel_eq_mul] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hb hC'₀)

end Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslatedMellin
