import Langlands.Analysis.SeveralComplex.CompactParameterStripGrowth
import Langlands.Global.RankinSelberg.ComplexLocalNormalizedGrowth
import Langlands.Global.RankinSelberg.ComplexPairParameterReflection
import Langlands.Global.RankinSelberg.ComplexPairStripRate

/-! # Strip growth in the continuation of complex pair normalizations -/

noncomputable section

open Metric Set
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SeveralComplex (compactParameterStripGrowth)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquet (HasComplexPairNormalizedGrowth)

private theorem norm_pairEpsilon_eq_of_re_eq (ds es : List ComplexCharacterData) (a : ℂˣ)
    {s t : ℂ} (h : s.re = t.re) :
    ‖(complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)‖ =
    ‖(complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) t : ℂ)‖ := by
  simp only [complexPairEpsilon, coe_complexEpsilon, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr a.ne_zero),
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.mul_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.sub_re, Complex.one_re, h]

private theorem compact_parameter_strip_bound (f : ℂ × ℂ → ℂ) (hf : Continuous f)
    (h : ∀ z : ℂ, ∀ s : ℂ, ‖f (z, s)‖ = ‖f (z, (s.re : ℂ))‖) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ball (0 : ℂ) 3, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f (z, s)‖ ≤ C := by
  let g (u : ℂ × ℝ) := f (u.1, (u.2 : ℂ))
  have hg : Continuous g := hf.comp (continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd))
  have hS : IsCompact (closedBall (0 : ℂ) 3 ×ˢ Icc a b) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun z hz s ha hb => by
    rw [h z s]
    exact (hC (z, s.re) ⟨ball_subset_closedBall hz, ⟨ha, hb⟩⟩).trans (le_max_left _ _)⟩

/-- Entire complex pair normalizations with strip growth propagate across a holomorphic
family if the ordinary integrals are jointly holomorphic and uniformly bounded on each
closed spectral strip in the common convergence half-plane. -/
def ComplexPairStripReflectionStatement : Prop :=
  ∀ (n m : ℕ) (l : Fin n → ℤ) (k : Fin m → ℤ) (p : ℂ → Fin n → ℂ) (q : ℂ → Fin m → ℂ)
    (a : ℂˣ) (c : ℂ), c ≠ 0 → Differentiable ℂ p → Differentiable ℂ q →
    ∀ (Z Zd : ℂ × ℂ → ℂ) (σ : ℝ),
      DifferentiableOn ℂ Z (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
      DifferentiableOn ℂ Zd (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
      (∀ x y : ℝ, σ < x → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ball (0 : ℂ) 3,
        ∀ s : ℂ, x ≤ s.re → s.re ≤ y → ‖Z (z, s)‖ ≤ C ∧ ‖Zd (z, s)‖ ≤ C) →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
        HasComplexPairNormalizedGrowth (characterList l (p z)) (characterList k (q z)) a c
          (fun s => Z (z, s)) (fun s => Zd (z, s))) →
      HasComplexPairNormalizedGrowth (characterList l (p 1)) (characterList k (q 1)) a c
        (fun s => Z (1, s)) (fun s => Zd (1, s))

set_option maxHeartbeats 600000 in
theorem complexPairStripReflection : ComplexPairStripReflectionStatement := by
  intro n m l k p q a c hc hp hq Z Zd σ hZ hZd hBound ⟨δ, hδ, hInit⟩
  let ds (z : ℂ) := characterList l (p z)
  let es (z : ℂ) := characterList k (q z)
  let P : Set ℂ := ball 0 3
  let R : Set ℂ := {s : ℂ | σ < s.re}
  let L : Set ℂ := {s : ℂ | s.re < 1 - σ}
  let ρ (s : ℂ) := 1 - s
  let F (u : ℂ × ℂ) := (complexPairLFactor (ds u.1) (es u.1)).denominator u.2 * Z u
  let G (u : ℂ × ℂ) := (complexPairLFactor ((ds u.1).map ComplexCharacterData.inv)
      ((es u.1).map ComplexCharacterData.inv)).denominator u.2 * Zd u
  let E (u : ℂ × ℂ) :=
    c * (complexPairEpsilon (ds u.1) (es u.1) a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) u.2 : ℂ)
  let H (u : ℂ × ℂ) := G (u.1, ρ u.2) / E u
  have hp' := hp.comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have hq' := hq.comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have hF : DifferentiableOn ℂ F (P ×ˢ R) :=
    (differentiable_pairDenominator l k _ _ hp' hq' _ differentiable_snd).differentiableOn.mul hZ
  have hG : DifferentiableOn ℂ G (P ×ˢ R) :=
    (differentiable_pairDualDenominator l k _ _ hp' hq' _ differentiable_snd).differentiableOn.mul hZd
  have hE : Differentiable ℂ E :=
    (differentiable_pairEpsilon l k _ _ hp' hq' a _ differentiable_snd).const_mul c
  have hE₀ (u : ℂ × ℂ) : E u ≠ 0 := mul_ne_zero hc (Units.ne_zero _)
  have hEn (z s : ℂ) : ‖E (z, s)‖ = ‖E (z, (s.re : ℂ))‖ := by
    simp only [E, norm_mul]
    rw [norm_pairEpsilon_eq_of_re_eq _ _ _ (Complex.ofReal_re s.re).symm]
  have hρd : Differentiable ℂ ρ := differentiable_id.const_sub 1
  have hρρ (s : ℂ) : ρ (ρ s) = s := sub_sub_cancel 1 s
  have hρre (s : ℂ) : (ρ s).re = 1 - s.re := by simp [ρ, Complex.sub_re]
  have hρim (s : ℂ) : |(ρ s).im| = |s.im| := by simp [ρ, Complex.sub_im]
  have hρ (s : ℂ) : ρ s ∈ R ↔ s ∈ L := by
    change (σ < (ρ s).re) ↔ s.re < 1 - σ
    rw [hρre]
    exact lt_sub_comm
  have hH : DifferentiableOn ℂ H (P ×ˢ L) := by
    have hcomp : Differentiable ℂ (fun u : ℂ × ℂ => (u.1, ρ u.2)) :=
      differentiable_fst.prodMk (hρd.comp differentiable_snd)
    have hGR : DifferentiableOn ℂ (fun u : ℂ × ℂ => G (u.1, ρ u.2)) (P ×ˢ L) :=
      hG.comp hcomp.differentiableOn fun u hu => ⟨hu.1, (hρ u.2).2 hu.2⟩
    exact hGR.mul (hE.differentiableOn.inv fun u _ => hE₀ u)
  let K : ℝ := ((n * m : ℕ) : ℝ) * Real.pi
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le
  have hDG (x y : ℝ) (hx : σ < x) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ P,
      ∀ s : ℂ, x ≤ s.re → s.re ≤ y →
        ‖F (z, s)‖ ≤ C * Real.exp (K * |s.im|) ∧ ‖G (z, s)‖ ≤ C * Real.exp (K * |s.im|) := by
    obtain ⟨B, hB, hB'⟩ := hBound x y hx
    obtain ⟨D, hD, hD'⟩ := complexPairStripRate ℂ (closedBall 0 3) (isCompact_closedBall _ _)
      n m l k p q hp.continuous hq.continuous x y
    refine ⟨D * B, mul_nonneg hD hB, fun z hz s hs ht => ?_⟩
    have hD₁ := hD' z (ball_subset_closedBall hz) s hs ht
    have hB₁ := hB' z hz s hs ht
    simp only [F, G, norm_mul]
    rw [mul_right_comm D B]
    exact ⟨mul_le_mul hD₁.1 hB₁.1 (norm_nonneg _) (by positivity),
      mul_le_mul hD₁.2 hB₁.2 (norm_nonneg _) (by positivity)⟩
  have hLeft (x y : ℝ) (hy : y < 1 - σ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ P,
      ∀ s : ℂ, x ≤ s.re → s.re ≤ y → ‖H (z, s)‖ ≤ C * Real.exp (K * |s.im|) := by
    obtain ⟨C, hC, hC'⟩ := hDG (1 - y) (1 - x) (lt_sub_comm.mp hy)
    obtain ⟨B, hB, hB'⟩ := compact_parameter_strip_bound (fun u => (E u)⁻¹)
      (hE.continuous.inv₀ hE₀) (fun z s => by simp only [norm_inv, hEn z s]) x y
    refine ⟨C * B, mul_nonneg hC hB, fun z hz s hs ht => ?_⟩
    have h := (hC' z hz (ρ s) (by rw [hρre]; linarith) (by rw [hρre]; linarith)).2
    rw [hρim] at h
    calc
      ‖H (z, s)‖ = ‖G (z, ρ s)‖ * ‖(E (z, s))⁻¹‖ := by simp only [H, div_eq_mul_inv, norm_mul]
      _ ≤ (C * Real.exp (K * |s.im|)) * B :=
        mul_le_mul h (hB' z hz s hs ht) (norm_nonneg _) (by positivity)
      _ = _ := mul_right_comm _ _ _
  obtain ⟨N, hN, hNg, hNF, hNH⟩ := compactParameterStripGrowth F H σ (1 - σ) K hK hF hH (by
    intro x y hx
    obtain ⟨C, hC, h⟩ := hDG x y hx
    exact ⟨C, hC, fun z hz s hs ht => (h z hz s hs ht).1⟩) hLeft (by
    refine ⟨min δ 1, lt_min hδ one_pos, fun z hz => ?_⟩
    have hzP : z ∈ P := ball_subset_ball ((min_le_right _ _).trans (by norm_num)) hz
    obtain ⟨U, V, hU, hV, hUg, _, ⟨τ, hτ⟩, hUV⟩ := hInit z (ball_subset_ball (min_le_left _ _) hz)
    have hfix : Differentiable ℂ (fun s : ℂ => (z, s)) :=
      (differentiable_const z).prodMk differentiable_id
    have hUR : EqOn U (fun s => F (z, s)) R :=
      Langlands.GeneralDirichlet.eqOn_halfPlane hU.differentiableOn
        (hF.comp hfix.differentiableOn fun _ hs => ⟨hzP, hs⟩) (fun s hs => (hτ s hs).1)
    have hVR : EqOn V (fun s => G (z, s)) R :=
      Langlands.GeneralDirichlet.eqOn_halfPlane hV.differentiableOn
        (hG.comp hfix.differentiableOn fun _ hs => ⟨hzP, hs⟩) (fun s hs => (hτ s hs).2)
    refine ⟨U, hU, hUg, hUR, fun s hs => ?_⟩
    change U s = G (z, ρ s) / E (z, s)
    apply (eq_div_iff (hE₀ (z, s))).2
    exact ((mul_comm _ _).trans (hUV s).symm).trans (hVR ((hρ s).2 hs)))
  let Nd (s : ℂ) := E (1, ρ s) * N (ρ s)
  have hNd : Differentiable ℂ Nd :=
    (hE.comp ((differentiable_const (1 : ℂ)).prodMk hρd)).mul (hN.comp hρd)
  have hNdg : HasStripExponentialGrowth Nd := by
    intro x y
    obtain ⟨C, K', T, hC, hK', hC'⟩ := hNg (1 - y) (1 - x)
    obtain ⟨B, hB, hB'⟩ := compact_parameter_strip_bound E hE.continuous hEn (1 - y) (1 - x)
    have h1 : (1 : ℂ) ∈ P := by simp [P, mem_ball, dist_eq_norm]
    refine ⟨B * C, K', T, mul_nonneg hB hC, hK', fun s hs ht hT => ?_⟩
    have hs' : 1 - y ≤ (ρ s).re := by rw [hρre]; linarith
    have ht' : (ρ s).re ≤ 1 - x := by rw [hρre]; linarith
    have h := hC' (ρ s) hs' ht' (by rwa [hρim])
    rw [hρim] at h
    change ‖E (1, ρ s) * N (ρ s)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hB' 1 h1 (ρ s) hs' ht') h (norm_nonneg _) hB
  refine ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨σ, fun s hs => ⟨hNF hs, ?_⟩⟩, fun s => ?_⟩
  · have hs' : ρ (ρ s) ∈ R := by rw [hρρ]; exact hs
    have h : N (ρ s) = H (1, ρ s) := hNH ((hρ (ρ s)).1 hs')
    change E (1, ρ s) * N (ρ s) = G (1, s)
    rw [h]
    simp only [H, hρρ]
    rw [mul_div_cancel₀ _ (hE₀ (1, ρ s))]
  · change E (1, ρ (ρ s)) * N (ρ (ρ s)) = _
    rw [hρρ]

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
