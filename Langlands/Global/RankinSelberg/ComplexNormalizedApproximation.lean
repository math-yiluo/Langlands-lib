import Langlands.Analysis.Complex.EntireStripExtension
import Langlands.Global.RankinSelberg.ComplexThetaNormalizedGrowth
import Langlands.Analysis.LandauDirichlet

/-! # Approximation in entire complex pair normalizations -/

noncomputable section

open Filter Set
open scoped Topology NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open Langlands.LocalFactor.Archimedean
open Langlands.Analysis (entireStripExtension)
open ArchimedeanInverseMellin (StripExpType)
open ArchimedeanComplexPairFactor (complexLFactor_stripExpType)
open ComplexWeightedKernelReflection (pairReflectionFactor)
open ComplexThetaNormalizedGrowth (stripExpType_pairReflectionFactor_inv)

/-- The sequence is uniformly Cauchy on each vertical line of the right half-plane.
The index of the Cauchy estimate may depend on that line. -/
def CauchyOnRightVerticalLines (σ : ℝ) (I : ℕ → ℂ → ℂ) : Prop :=
  ∀ b : ℝ, σ < b → ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ n m : ℕ, k ≤ n → k ≤ m →
    ∀ s : ℂ, s.re = b → ‖I n s - I m s‖ ≤ ε

private theorem lineBound_of_stripExpType {w : ℂ → ℂ} (hw : StripExpType w) (x : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ s : ℂ, s.re = x → ‖w s‖ ≤ C * Real.exp (K * |s.im|) := by
  obtain ⟨C, K, hC, hK, h⟩ := hw x x
  refine ⟨C, K, hC, hK, fun s hs => ?_⟩
  have h' := h x le_rfl le_rfl s.im
  rw [← hs, Complex.re_add_im] at h'
  exact h'

private theorem mul_le_exp_of_lineBound {C K : ℝ} (hC : 0 ≤ C) {w x : ℂ} {e : ℝ}
    (he : 0 < e) (hw : ‖w‖ ≤ C * Real.exp K) (hx : ‖x‖ ≤ e / (C + 1)) :
    ‖w * x‖ ≤ e * Real.exp K := by
  have hD : 0 < C + 1 := by linarith
  rw [norm_mul]
  refine (mul_le_mul hw hx (norm_nonneg _) (by positivity)).trans ?_
  calc
    _ = (C * (e / (C + 1))) * Real.exp K := by ring
    _ ≤ e * Real.exp K := by
      gcongr
      rw [← mul_div_assoc, div_le_iff₀ hD]
      nlinarith

/-- The normalized functional equations turn separate Cauchy estimates for the ordinary
and dual right half-plane integrals into a locally uniform entire limit. -/
def ComplexPairNormalizedApproximationStatement : Prop :=
  ∀ (ds es : List ComplexCharacterData) (a : ℂˣ) (c : ℂ), c ≠ 0 →
  ∀ (σ : ℝ) (I Id : ℕ → ℂ → ℂ) (J : ℂ → ℂ),
    (∀ n, HasComplexPairNormalizedGrowth ds es a c (I n) (Id n)) →
    (∀ n, DifferentiableOn ℂ (I n) {s : ℂ | σ < s.re}) →
    (∀ n, DifferentiableOn ℂ (Id n) {s : ℂ | σ < s.re}) →
    CauchyOnRightVerticalLines σ I → CauchyOnRightVerticalLines σ Id →
    (∀ s : ℂ, σ < s.re → Tendsto (fun n => I n s) atTop (𝓝 (J s))) →
    ∃ (N : ℕ → ℂ → ℂ) (N₀ : ℂ → ℂ),
      (∀ n, Differentiable ℂ (N n)) ∧
      (∀ n s, σ < s.re → N n s = (complexPairLFactor ds es).denominator s * I n s) ∧
      TendstoLocallyUniformly N N₀ atTop ∧ Differentiable ℂ N₀ ∧
      HasStripExponentialGrowth N₀ ∧
      ∀ s : ℂ, σ < s.re → N₀ s = (complexPairLFactor ds es).denominator s * J s

theorem complexPairNormalizedApproximation : ComplexPairNormalizedApproximationStatement := by
  intro ds es a c hc σ I Id J hPair hI hId hCI hCId hJ
  let L := complexPairLFactor ds es
  let Ld := complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
  let E := pairReflectionFactor ds es a c
  let W (s : ℂ) := Ld.denominator (1 - s) * (E s)⁻¹
  have hE (s : ℂ) : E s ≠ 0 := mul_ne_zero hc (Units.ne_zero _)
  choose N Nd hN hNd hNg _ hR hFE using hPair
  have hNR (n : ℕ) : EqOn (N n) (fun s => L.denominator s * I n s) {s : ℂ | σ < s.re} := by
    obtain ⟨b, hb⟩ := hR n
    exact Langlands.GeneralDirichlet.eqOn_halfPlane (hN n).differentiableOn
      (L.entire.differentiableOn.mul (hI n)) (fun s hs => (hb s hs).1)
  have hNdR (n : ℕ) : EqOn (Nd n) (fun s => Ld.denominator s * Id n s) {s : ℂ | σ < s.re} := by
    obtain ⟨b, hb⟩ := hR n
    exact Langlands.GeneralDirichlet.eqOn_halfPlane (hNd n).differentiableOn
      (Ld.entire.differentiableOn.mul (hId n)) (fun s hs => (hb s hs).2)
  have hNL (n : ℕ) (s : ℂ) (hs : s.re < 1 - σ) : N n s = W s * Id n (1 - s) := by
    have hs' : (1 - s : ℂ) ∈ {s : ℂ | σ < s.re} := by
      change σ < (1 - s : ℂ).re
      rw [Complex.sub_re, Complex.one_re]
      linarith
    apply mul_left_cancel₀ (hE s)
    calc
      E s * N n s = Nd n (1 - s) := (hFE n s).symm
      _ = Ld.denominator (1 - s) * Id n (1 - s) := hNdR n hs'
      _ = E s * (W s * Id n (1 - s)) := by
        dsimp only [W]
        field_simp [hE s]
  have hWt : StripExpType W := by
    have hLdt : StripExpType Ld.denominator := complexLFactor_stripExpType _
    refine ((((hLdt.comp_add 1).comp_ofReal_mul (-1)).mul
      (stripExpType_pairReflectionFactor_inv ds es a c))).congr fun s => ?_
    simp [W, E, sub_eq_add_neg, add_comm]
  have hLt : StripExpType L.denominator := complexLFactor_stripExpType _
  obtain ⟨N₀, hLim, hN₀, hN₀g⟩ := entireStripExtension N hN hNg (by
    intro u v _
    let x := min u (1 - σ) - 1
    let y := max v σ + 1
    have hx : x < u := by dsimp [x]; linarith [min_le_left u (1 - σ)]
    have hx' : x < 1 - σ := by dsimp [x]; linarith [min_le_right u (1 - σ)]
    have hy : v < y := by dsimp [y]; linarith [le_max_left v σ]
    have hy' : σ < y := by dsimp [y]; linarith [le_max_right v σ]
    obtain ⟨C, K, hC, _, hWR⟩ := lineBound_of_stripExpType hLt y
    obtain ⟨D, M, hD, _, hWL⟩ := lineBound_of_stripExpType hWt x
    refine ⟨x, y, max K M, hx, hy, fun ε hε => ?_⟩
    obtain ⟨k, hk⟩ := hCI y hy' (ε / (C + 1)) (by positivity)
    obtain ⟨l, hl⟩ := hCId (1 - x) (by linarith) (ε / (D + 1)) (by positivity)
    refine ⟨max k l, fun n m hn hm s hs => ?_⟩
    rcases hs with hs | hs
    · rw [hNL n s (hs.trans_lt hx'), hNL m s (hs.trans_lt hx'), ← mul_sub]
      have hRe : (1 - s : ℂ).re = 1 - x := by simp [Complex.sub_re, hs]
      have h := mul_le_exp_of_lineBound hD hε (hWL s hs)
        (hl n m ((le_max_right _ _).trans hn) ((le_max_right _ _).trans hm) (1 - s) hRe)
      exact h.trans (by gcongr; exact le_max_right _ _)
    · have hs' : s ∈ {s : ℂ | σ < s.re} := by
        change σ < s.re
        rwa [hs]
      rw [hNR n hs', hNR m hs', ← mul_sub]
      have h := mul_le_exp_of_lineBound hC hε (hWR s hs)
        (hk n m ((le_max_left _ _).trans hn) ((le_max_left _ _).trans hm) s hs)
      exact h.trans (by gcongr; exact le_max_left _ _))
  refine ⟨N, N₀, hN, fun n s hs => hNR n hs, hLim, hN₀, hN₀g, fun s hs => ?_⟩
  have hLim' : Tendsto (fun n => N n s) atTop (𝓝 (N₀ s)) :=
    hLim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ s)
  have hJ' := (hJ s hs).const_mul (L.denominator s)
  simp only [show (fun n => N n s) = fun n => L.denominator s * I n s from
    funext fun n => hNR n hs] at hLim'
  exact tendsto_nhds_unique hLim' hJ'

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
