import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Global.Factors.CuspidalPairPoleFiniteEuler
import Langlands.LocalFactor.Archimedean.GammaStripGrowth
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-! # Bounds of the completed pair product on far-right strips -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField Polynomial Set Filter

namespace Langlands.Global.CuspidalPairPoles

open LocalFactor LocalFactor.Archimedean
open CompletionPadic CuspidalPairFunctionalEquation CuspidalPairEulerConvergence
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)

variable {F : Type*} [Field F] [NumberField F]

private theorem exists_exceptional_finiteL_bound (v : FinitePlace F) (L : ℂ[X])
    (hL : L.eval 0 = 1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ‖(L.eval (RankinSelberg.spectralPoint
      (residueCardinality v) s))⁻¹‖ ≤ 2 := by
  let U : Set ℂ := {x | ‖L.eval x - 1‖ < 1 / 2}
  have hU : IsOpen U := isOpen_lt (L.continuous.sub continuous_const).norm continuous_const
  have h0 : 0 ∈ U := by change ‖L.eval 0 - 1‖ < _; rw [hL, sub_self, norm_zero]; norm_num
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  have hq : (1 : ℝ) < residueCardinality v := by
    exact_mod_cast (show 1 < residueCardinality v from two_le_residueCardinality v)
  have hlim := (tendsto_rpow_atBot_of_base_gt_one _ hq).comp tendsto_neg_atTop_atBot
  obtain ⟨σ, hσ⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨σ, fun s hs => ?_⟩
  let x := RankinSelberg.spectralPoint (residueCardinality v) s
  have hx : x ∈ U := hball (by
    simpa only [Metric.mem_ball, dist_zero_right, x, norm_spectralPoint, Function.comp_def]
      using hσ s.re hs.le)
  have hb : (1 / 2 : ℝ) ≤ ‖L.eval x‖ := by
    change ‖L.eval x - 1‖ < 1 / 2 at hx
    have h := norm_sub_norm_le (1 : ℂ) (L.eval x)
    rw [norm_one, norm_sub_rev] at h
    linarith
  rw [norm_inv]
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  convert (inv_le_inv₀ (hhalf.trans_le hb) hhalf).mpr hb using 1
  norm_num

private theorem norm_spherical_factor_le {n m : ℕ} (v : FinitePlace F)
    (a : Unramified.Eigenvalues n) (b : Unramified.Eigenvalues m) {A B : ℝ}
    (hA : ∀ α ∈ (a : Multiset ℂˣ), ‖(α : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ A)
    (hB : ∀ β ∈ (b : Multiset ℂˣ), ‖(β : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ B)
    {s : ℂ} (hs : A + B + ((n * m + 2 : ℕ) : ℝ) < s.re) :
    ‖((pairEulerPolynomial a b).eval (RankinSelberg.spectralPoint
      (residueCardinality v) s))⁻¹‖ ≤
      1 + 2 ^ (n * m + 1) * (residueCardinality v : ℝ) ^ (-((n * m + 2 : ℕ) : ℝ)) := by
  let q : ℝ := residueCardinality v
  let x := RankinSelberg.spectralPoint (residueCardinality v) s
  let d : ℕ := n * m + 2
  have hq2 : 2 ≤ q := by
    dsimp only [q]
    exact_mod_cast two_le_residueCardinality v
  have hq0 : 0 < q := by linarith
  have hab (α : ℂˣ) (hα : α ∈ (a : Multiset ℂˣ)) (β : ℂˣ) (hβ : β ∈ (b : Multiset ℂˣ)) :
      ‖(α : ℂ) * β * x‖ ≤ q ^ (-(d : ℝ)) := by
    rw [norm_mul, norm_mul, norm_spectralPoint]
    calc
      _ ≤ q ^ A * q ^ B * q ^ (-s.re) := by gcongr; exacts [hA α hα, hB β hβ]
      _ = q ^ (A + B - s.re) := by rw [sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_add hq0]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [d]; linarith)
  have hsmall : 2 ^ (n * m) * q ^ (-(d : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg hq0.le, Real.rpow_natCast]
    calc
      _ ≤ (2 : ℝ) ^ (n * m) * ((2 : ℝ) ^ d)⁻¹ := by gcongr
      _ ≤ _ := by
        dsimp [d]
        rw [pow_add, pow_two]
        field_simp
        nlinarith [pow_pos (by norm_num : 0 < (2 : ℝ)) (n * m)]
  have hdiff := norm_inv_eval_pairEulerPolynomial_sub_one_le a b x
    (Real.rpow_nonneg hq0.le _) hab hsmall
  have hnorm := (norm_sub_norm_le (((pairEulerPolynomial a b).eval x)⁻¹) (1 : ℂ)).trans hdiff
  rw [norm_one] at hnorm
  exact (sub_le_iff_le_add.mp hnorm).trans_eq (add_comm _ _)

section Finite

universe uQ

variable [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{_, uQ} T} {P' : CuspidalSpectralPresentation.{_, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}

/-- The full finite Euler product of any certified choice is uniformly bounded
on a sufficiently far right half-plane. -/
theorem FinitePairLChoice.exists_norm_tprod_le_right (c : FinitePairLChoice P P' h h') :
    ∃ σ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, σ < s.re → ‖∏' v, c.finiteL v s‖ ≤ M := by
  classical
  let S := P.exceptional ∪ P'.exceptional
  have hP : P.exceptional ⊆ S := Finset.subset_union_left
  have hP' : P'.exceptional ⊆ S := Finset.subset_union_right
  obtain ⟨a, ha⟩ := RankinSelbergGlobal.exists_hasSatakeBound_presentation T P
  obtain ⟨b, hb⟩ := RankinSelbergGlobal.exists_hasSatakeBound_presentation T' P'
  have hL (v : FinitePlace F) : (c.lPolynomial v).eval 0 = 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, hv⟩ := c.lPolynomial_spec v
    rw [← Polynomial.coeff_zero_eq_eval_zero, hv.coeff_zero]
  choose σe hσe using (fun v : ↥(S : Set (FinitePlace F)) =>
    exists_exceptional_finiteL_bound v.1 (c.lPolynomial v.1) (hL v.1))
  obtain ⟨σE, hσE⟩ := (Set.finite_range σe).bddAbove
  obtain ⟨σF, hσF⟩ := c.exists_finiteL_convergence hP hP'
  let d : ℕ := (r + 1) * (t + 1) + 2
  let M₀ (v : FinitePlace F) : ℝ :=
    2 ^ ((r + 1) * (t + 1) + 1) * (residueCardinality v : ℝ) ^ (-(d : ℝ))
  let M (v : FinitePlace F) := M₀ v + ((S : Set (FinitePlace F)).indicator fun _ => (1 : ℝ)) v
  have hM₀ : Summable M₀ := by
    have hd : (1 : ℝ) < d := by exact_mod_cast (show 1 < d from by dsimp [d]; omega)
    simpa only [M₀, residueCardinality_eq_absNorm] using
      (HeckeEulerProduct.summable_absNorm_rpow (K := F) hd).mul_left
        (2 ^ ((r + 1) * (t + 1) + 1))
  have hMi : Summable ((S : Set (FinitePlace F)).indicator fun _ => (1 : ℝ)) :=
    summable_of_ne_finset_zero (s := S) (fun v hv => Set.indicator_of_notMem hv _)
  have hM : Summable M := hM₀.add hMi
  have hM₀_nn (v : FinitePlace F) : 0 ≤ M₀ v := by dsimp [M₀]; positivity
  have hM_nn (v : FinitePlace F) : 0 ≤ M v :=
    add_nonneg (hM₀_nn v) (Set.indicator_nonneg (fun _ _ => zero_le_one) v)
  refine ⟨max (max (a + b + (d : ℝ)) σE) σF, Real.exp (∑' v, M v), (Real.exp_pos _).le,
    fun s hs => ?_⟩
  have hlocal (v : FinitePlace F) : ‖c.finiteL v s‖ ≤ 1 + M v := by
    by_cases hv : v ∈ S
    · have hvE : σe ⟨v, hv⟩ ≤ max (max (a + b + (d : ℝ)) σE) σF :=
        ((hσE (Set.mem_range_self ⟨v, hv⟩)).trans (le_max_right _ _)).trans (le_max_left _ σF)
      refine (hσe ⟨v, hv⟩ s (hvE.trans_lt hs)).trans ?_
      simp only [M, Set.indicator_of_mem hv]
      linarith [hM₀_nn v]
    · have hvP : v ∉ P.exceptional := fun hx => hv (hP hx)
      have hvP' : v ∉ P'.exceptional := fun hx => hv (hP' hx)
      have hσ : a + b + (d : ℝ) < s.re := ((le_max_left _ σE).trans (le_max_left _ σF)).trans_lt hs
      simpa only [c.finiteL_eq_partialEulerFactor hP hP' ⟨v, hv⟩,
        CuspidalPairBoundaryNonvanishing.partialEulerFactor, M, Set.indicator_of_notMem hv, add_zero, M₀]
        using norm_spherical_factor_le v _ _ (ha v hvP) (hb v hvP') hσ
  have hp := (hσF s ((le_max_right _ σF).trans_lt hs)).2
  rw [hp.tprod_eq]
  refine hasProd_le_of_prod_le hp.norm (fun E => ?_)
  calc
    _ ≤ ∏ v ∈ E, Real.exp (M v) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun v _ => (hlocal v).trans (by simpa only [add_comm] using Real.add_one_le_exp (M v)))
    _ = Real.exp (∑ v ∈ E, M v) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hM.sum_le_tsum E fun v _ => hM_nn v)

end Finite

private def HasRightStripBounds (f : ℂ → ℂ) : Prop :=
  ∃ σ : ℝ, ∀ a b : ℝ, σ < a → ∃ M : ℝ, 0 ≤ M ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ M

private theorem HasRightStripBounds.one : HasRightStripBounds (fun _ => 1) :=
  ⟨0, fun _ _ _ => ⟨1, zero_le_one, fun _ _ _ => norm_one.le⟩⟩

private theorem HasRightStripBounds.mul {f g : ℂ → ℂ}
    (hf : HasRightStripBounds f) (hg : HasRightStripBounds g) :
    HasRightStripBounds (fun s => f s * g s) := by
  obtain ⟨σ, hσ⟩ := hf
  obtain ⟨τ, hτ⟩ := hg
  refine ⟨max σ τ, fun a b ha => ?_⟩
  obtain ⟨C, hC, hCf⟩ := hσ a b ((le_max_left _ _).trans_lt ha)
  obtain ⟨D, hD, hDg⟩ := hτ a b ((le_max_right _ _).trans_lt ha)
  refine ⟨C * D, mul_nonneg hC hD, fun s hl hr => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hCf s hl hr) (hDg s hl hr) (norm_nonneg _) hC

private theorem hasRightStripBounds_prod {ι : Type*} (E : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ E, HasRightStripBounds (f i)) :
    HasRightStripBounds (fun s => ∏ i ∈ E, f i s) := by
  classical
  induction E using Finset.induction_on with
  | empty => simpa using HasRightStripBounds.one
  | insert i E hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i E)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem hasRightStripBounds_gammaBlock (b : GammaBlock) :
    HasRightStripBounds (fun s => (b.factor.denominator s)⁻¹) := by
  cases b with
  | real δ =>
    refine ⟨-δ.re, fun a b ha => ?_⟩
    obtain ⟨M, hM, hbound⟩ := norm_Gamma_le_on_strip (b := (b + δ.re) / 2)
      (a := (a + δ.re) / 2) (by linarith)
    refine ⟨M, hM, fun s hl hr => ?_⟩
    have hre : ((s + δ) / (2 : ℂ)).re = (s.re + δ.re) / 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re, Complex.add_re]
    have hΓ := hbound ((s + δ) / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
    have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
    change ‖((Complex.Gammaℝ (s + δ))⁻¹)⁻¹‖ ≤ M
    rw [inv_inv, Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply le_trans (mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hπ ?_)
      (norm_nonneg _))
    · simpa only [one_mul] using hΓ
    · rw [neg_div, Complex.neg_re, hre]; linarith
  | complex δ =>
    refine ⟨-δ.re, fun a b ha => ?_⟩
    obtain ⟨M, hM, hbound⟩ := norm_Gamma_le_on_strip (b := b + δ.re)
      (a := a + δ.re) (by linarith)
    refine ⟨2 * M, by positivity, fun s hl hr => ?_⟩
    have hΓ := hbound (s + δ) (by rw [Complex.add_re]; linarith)
      (by rw [Complex.add_re]; linarith)
    have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.one_le_pi_div_two]
    change ‖((Complex.Gammaℂ (s + δ))⁻¹)⁻¹‖ ≤ 2 * M
    rw [inv_inv, Complex.Gammaℂ_def, norm_mul, norm_mul, Complex.norm_two,
      ← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hπ)]
    have hexp : (-(s + δ)).re ≤ 0 := by rw [Complex.neg_re, Complex.add_re]; linarith
    calc
      _ ≤ 2 * 1 * M := by gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos hπ hexp
      _ = _ := by ring

private theorem hasRightStripBounds_gammaProduct (bs : List GammaBlock) :
    HasRightStripBounds (fun s => ((gammaProduct bs).denominator s)⁻¹) := by
  induction bs with
  | nil => simpa [gammaProduct, ReciprocalEntire.product, ReciprocalEntire.one] using
      HasRightStripBounds.one
  | cons b bs ih =>
    change HasRightStripBounds (fun s =>
      (b.factor.denominator s * (gammaProduct bs).denominator s)⁻¹)
    simpa only [mul_inv] using (hasRightStripBounds_gammaBlock b).mul ih

private theorem hasRightStripBounds_archimedeanPairProduct
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData) :
    HasRightStripBounds (archimedeanPairProduct dR dR' dC dC') := by
  classical
  unfold archimedeanPairProduct
  refine (hasRightStripBounds_prod Finset.univ _ (fun v _ => ?_)).mul
    (hasRightStripBounds_prod Finset.univ _ (fun v _ => ?_))
  · rw [realPairLFactor, realLFactor_eq_gammaProduct]
    exact hasRightStripBounds_gammaProduct _
  · rw [complexPairLFactor, complexLFactor_eq_gammaProduct]
    exact hasRightStripBounds_gammaProduct _

section Completed

universe u uQ

/-- The completed pair product is bounded on every strip that is sufficiently far
to the right. -/
def CompletedPairRightStripBounds : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (Λ : ℂ → ℂ),
    c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ →
    ∃ σ : ℝ, ∀ a b : ℝ, σ < a → ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ M

/-- The uniform finite Euler bound and the Gamma integral on the positive half-plane
give the bound for the completed function on its initial strips. -/
theorem completedPairRightStripBounds : CompletedPairRightStripBounds.{u, uQ} := by
  intro F _ _ _ r t T T' P P' h h' c dR dR' dC dC' Λ hΛ
  obtain ⟨σL, hσL⟩ := hΛ
  obtain ⟨σF, C, hC, hσF⟩ := c.exists_norm_tprod_le_right
  obtain ⟨σA, hσA⟩ := hasRightStripBounds_archimedeanPairProduct dR dR' dC dC'
  refine ⟨max (max σL σF) σA, fun a b ha => ?_⟩
  obtain ⟨D, hD, hbound⟩ := hσA a b ((le_max_right _ _).trans_lt ha)
  refine ⟨D * C, mul_nonneg hD hC, fun s hl hr => ?_⟩
  have hsL : σL < s.re := ((le_max_left _ σF).trans (le_max_left _ σA)).trans_lt (ha.trans_le hl)
  have hsF : σF < s.re := ((le_max_right σL _).trans (le_max_left _ σA)).trans_lt (ha.trans_le hl)
  obtain ⟨_, p, hp, heq⟩ := hσL s hsL
  rw [heq, ← hp.tprod_eq, norm_mul]
  exact mul_le_mul (hbound s hl hr) (hσF s hsF) (norm_nonneg _) hD

end Completed

end Langlands.Global.CuspidalPairPoles
