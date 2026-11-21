import Langlands.Global.RankinSelberg.RealBlockParameters
import Langlands.LocalFactor.Archimedean.GammaStripGrowth

/-! # A common reciprocal Gamma rate for real pair denominators of compact exponent families -/

noncomputable section

open Set
open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealBlockParameters

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

/-- The real reciprocal Gamma block has rate `π` on each closed vertical strip. -/
theorem norm_gammaReal_denominator_le_exp (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖gammaReal.denominator s‖ ≤ C * Real.exp (Real.pi * |s.im|) := by
  obtain ⟨C, hC, h⟩ := norm_inv_Gamma_le_exp_of_one_le (a / 2) (b / 2)
  let R := max |a| |b| + 2
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (gammaReal.entire.continuous.continuousOn)
  let A := C * (Real.pi ^ (a / 2) + Real.pi ^ (b / 2))
  have hA : 0 ≤ A := by positivity
  refine ⟨max (max B 0) A, (le_max_right B 0).trans (le_max_left _ _), fun s hs ht => ?_⟩
  by_cases hi : 2 ≤ |s.im|
  · change ‖(Complex.Gammaℝ s)⁻¹‖ ≤ _
    have hre : (s / 2).re = s.re / 2 := by simp
    have him : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
    have hg : ‖(Complex.Gamma (s / 2))⁻¹‖ ≤ C * Real.exp (Real.pi * (|s.im| / 2)) := by
      have := h (s / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; linarith)
      rwa [him] at this
    have hpow : ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ = Real.pi ^ (s.re / 2) := by
      rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      have : (-s / 2).re = -(s.re / 2) := by simp [neg_div]
      rw [this, Real.rpow_neg Real.pi_pos.le, inv_inv]
    have hp : Real.pi ^ (s.re / 2) ≤ Real.pi ^ (a / 2) + Real.pi ^ (b / 2) :=
      ArchimedeanInverseMellin.rpow_le_add Real.pi_pos (by linarith) (by linarith)
    rw [Complex.Gammaℝ_def, mul_inv, norm_mul, hpow]
    have hexp : Real.exp (Real.pi * (|s.im| / 2)) ≤ Real.exp (Real.pi * |s.im|) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg s.im, Real.pi_pos])
    calc
      _ ≤ (Real.pi ^ (a / 2) + Real.pi ^ (b / 2)) * (C * Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul hp (hg.trans (mul_le_mul_of_nonneg_left hexp hC)) (norm_nonneg _)
          (by positivity)
      _ = A * Real.exp (Real.pi * |s.im|) := by dsimp only [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have hr : |s.re| ≤ max |a| |b| := abs_le.mpr
      ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hs),
        ht.trans ((le_abs_self b).trans (le_max_right _ _))⟩
    have hsR : s ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr <|
      (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hr (le_of_not_ge hi))
    exact (hB s hsR).trans <| (le_max_left B 0).trans <|
      (le_max_left (max B 0) A).trans <| le_mul_of_one_le_right
        ((le_max_right B 0).trans (le_max_left _ _)) (Real.one_le_exp (by positivity))

/-- A rate-`π` bound on all strips survives a fixed translation and a bounded parameter shift. -/
private theorem shift_rate {G : ℂ → ℂ}
    (hG : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖G s‖ ≤ C * Real.exp (Real.pi * |s.im|)) (κ : ℂ) (u v R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, ‖w‖ ≤ R → ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖G (s + w + κ)‖ ≤ A * Real.exp (Real.pi * |s.im|) := by
  let R' := R + ‖κ‖
  obtain ⟨C, hC, h⟩ := hG (u - R') (v + R')
  refine ⟨C * Real.exp (Real.pi * R'), by positivity, fun w hw s hs ht => ?_⟩
  have hwk : ‖w + κ‖ ≤ R' := (norm_add_le _ _).trans (by dsimp only [R']; linarith)
  have hre := (Complex.abs_re_le_norm (w + κ)).trans hwk
  have him := (Complex.abs_im_le_norm (w + κ)).trans hwk
  have hre' := abs_le.mp hre
  have hz : s + w + κ = s + (w + κ) := add_assoc _ _ _
  rw [hz]
  refine (h _ (by rw [Complex.add_re]; linarith) (by rw [Complex.add_re]; linarith)).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  rw [Complex.add_im]
  have hi := (abs_add_le s.im (w + κ).im).trans (add_le_add le_rfl him)
  nlinarith [Real.pi_pos]

/-- Each parametrized block denominator has rate `π` on every strip, uniformly for bounded
exponents. -/
theorem norm_block_denominator_le (x : Shape) (u v R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, ‖w‖ ≤ R → ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖(blockOfParams x 0).lFactor.denominator (s + w)‖ ≤ A * Real.exp (Real.pi * |s.im|) := by
  cases x with
  | inl e =>
    obtain ⟨A, hA, h⟩ := shift_rate norm_gammaReal_denominator_le_exp (0 + (e.val : ℂ)) u v R
    refine ⟨A, hA, fun w hw s hs ht => ?_⟩
    simpa only [blockOfParams, RealBlock.lFactor_character, ReciprocalEntire.denominator_shift,
      charData_exponent, charData_parity] using h w hw s hs ht
  | inr l =>
    obtain ⟨A, hA, h⟩ := shift_rate norm_gammaComplex_denominator_le_exp
      (0 + (l.natAbs : ℂ) / 2) u v R
    refine ⟨A, hA, fun w hw s hs ht => ?_⟩
    simpa only [blockOfParams, RealBlock.lFactor_induced, ReciprocalEntire.denominator_shift,
      Langlands.Archimedean.characterOfParams_exponent,
      Langlands.Archimedean.characterOfParams_weight] using h w hw s hs ht

/-- The number of blocks of the pair presentation of two parametrized lists. -/
def blockCount {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape) : ℕ :=
  ∑ i, ∑ j, (tensorShape (sh i) (sh' j)).length

theorem length_tensorShape_dual (x y : Shape) :
    (tensorShape (dualShape x) (dualShape y)).length = (tensorShape x y).length := by
  cases x <;> cases y <;> rfl

theorem blockCount_dual {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape) :
    blockCount (fun i => dualShape (sh i)) (fun j => dualShape (sh' j)) = blockCount sh sh' := by
  simp only [blockCount, length_tensorShape_dual]

private theorem norm_listProd_le {I : Type*} (l : List I) (f : I → ℂ) (A : I → ℝ) (E : ℝ)
    (hA : ∀ x ∈ l, 0 ≤ A x) (hE : 0 ≤ E) (h : ∀ x ∈ l, ‖f x‖ ≤ A x * E) :
    ‖(l.map f).prod‖ ≤ (l.map A).prod * E ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul, pow_succ]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => hA y (List.mem_cons_of_mem x hy))
      (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hl : 0 ≤ (l.map A).prod := List.prod_nonneg fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact hA z (List.mem_cons_of_mem x hz)
    calc
      _ ≤ (A x * E) * ((l.map A).prod * E ^ l.length) :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (hA x List.mem_cons_self) hE)
      _ = _ := by ring

/-- On a compact set of exponent parameters, the pair denominator has a common exponential
rate `blockCount · π` on every closed vertical strip. -/
theorem norm_pairDenominator_le {X : Type*} [TopologicalSpace X] (S : Set X) (hS : IsCompact S)
    {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape) (p : X → Fin n → ℂ)
    (q : X → Fin m → ℂ) (hp : Continuous p) (hq : Continuous q) (u v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖(realPairLFactor (blockList sh (p z)) (blockList sh' (q z))).denominator s‖ ≤
        C * Real.exp ((blockCount sh sh' : ℝ) * Real.pi * |s.im|) := by
  obtain ⟨Rp, hRp⟩ := hS.exists_bound_of_continuousOn hp.continuousOn
  obtain ⟨Rq, hRq⟩ := hS.exists_bound_of_continuousOn hq.continuousOn
  let R := Rp + Rq
  choose A hA0 hA using fun x : Shape => norm_block_denominator_le x u v R
  let B := ∏ i, ∏ j, ((tensorShape (sh i) (sh' j)).map A).prod
  have hBn : ∀ i j, 0 ≤ ((tensorShape (sh i) (sh' j)).map A).prod := fun i j =>
    List.prod_nonneg fun y hy => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
      exact hA0 z
  have hB : 0 ≤ B := Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hBn i j
  refine ⟨B, hB, fun z hz s hs ht => ?_⟩
  let E := Real.exp (Real.pi * |s.im|)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hw (i : Fin n) (j : Fin m) : ‖p z i + q z j‖ ≤ R :=
    (norm_add_le _ _).trans (add_le_add ((norm_le_pi_norm (p z) i).trans (hRp z hz))
      ((norm_le_pi_norm (q z) j).trans (hRq z hz)))
  rw [pairDenominator_blockList, norm_prod]
  have hstep : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ‖∏ j, ((tensorShape (sh i) (sh' j)).map fun b =>
        (blockOfParams b 0).lFactor.denominator (s + (p z i + q z j))).prod‖ ≤
        ∏ j, (((tensorShape (sh i) (sh' j)).map A).prod *
          E ^ (tensorShape (sh i) (sh' j)).length) := by
    intro i _
    rw [norm_prod]
    refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
    exact norm_listProd_le _ _ _ _ (fun x _ => hA0 x) hE
      (fun x _ => hA x _ (hw i j) s hs ht)
  refine (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hstep).trans_eq ?_
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  dsimp only [B, E, blockCount]
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The pair denominator and the dual pair denominator have the common rate
`blockCount · π` on every strip, uniformly on a compact parameter set. -/
def RealPairStripRateStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (S : Set X), IsCompact S →
    ∀ (n m : ℕ) (sh : Fin n → Shape) (sh' : Fin m → Shape)
      (p : X → Fin n → ℂ) (q : X → Fin m → ℂ), Continuous p → Continuous q →
    ∀ u v : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖(realPairLFactor (blockList sh (p z)) (blockList sh' (q z))).denominator s‖ ≤
        C * Real.exp ((blockCount sh sh' : ℝ) * Real.pi * |s.im|) ∧
      ‖(realPairLFactor ((blockList sh (p z)).map RealLocalJacquet.dualBlock)
        ((blockList sh' (q z)).map RealLocalJacquet.dualBlock)).denominator s‖ ≤
        C * Real.exp ((blockCount sh sh' : ℝ) * Real.pi * |s.im|)

theorem realPairStripRate : RealPairStripRateStatement := by
  intro X _ S hS n m sh sh' p q hp hq u v
  obtain ⟨C, hC, hCp⟩ := norm_pairDenominator_le S hS sh sh' p q hp hq u v
  obtain ⟨D, hD, hDp⟩ := norm_pairDenominator_le S hS (fun i => dualShape (sh i))
    (fun j => dualShape (sh' j)) (fun z i => -p z i) (fun z j => -q z j)
    (continuous_pi fun i => ((continuous_apply i).comp hp).neg)
    (continuous_pi fun j => ((continuous_apply j).comp hq).neg) u v
  refine ⟨max C D, hC.trans (le_max_left _ _), fun z hz s hs ht => ⟨?_, ?_⟩⟩
  · exact (hCp z hz s hs ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left C D) (Real.exp_pos _).le)
  · rw [map_dualBlock_blockList, map_dualBlock_blockList]
    have h := hDp z hz s hs ht
    rw [blockCount_dual] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right C D) (Real.exp_pos _).le)

end Langlands.Global.RankinSelbergGlobal.RealBlockParameters
