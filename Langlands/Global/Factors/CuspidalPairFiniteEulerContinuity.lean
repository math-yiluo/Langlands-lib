import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.Global.RankinSelberg.PartialEulerProductConvergence
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Continuity of the finite pair Euler product -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u uQ

namespace Langlands.Global.CuspidalPairPoles.FinitePairLChoice

open NumberField Polynomial Filter Set CompletionPadic CuspidalPairFunctionalEquation
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairEulerConvergence
open scoped _root_.Topology

variable {F : Type u} [Field F] [NumberField F]

private theorem spectralPoint_eventually_small (v : FinitePlace F) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      ‖RankinSelberg.spectralPoint (residueCardinality v) s‖ < ε := by
  have hq : (1 : ℝ) < residueCardinality v := by
    exact_mod_cast (show 1 < residueCardinality v from two_le_residueCardinality v)
  have hlim := (tendsto_rpow_atBot_of_base_gt_one _ hq).comp tendsto_neg_atTop_atBot
  obtain ⟨σ, hσ⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  exact ⟨σ, fun s hs => by simpa only [norm_spectralPoint, Function.comp_def] using hσ s.re hs.le⟩

private theorem exists_exceptional_abscissa (v : FinitePlace F) (L : ℂ[X]) (hL : L.eval 0 ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      L.eval (RankinSelberg.spectralPoint (residueCardinality v) s) ≠ 0 := by
  have hopen : IsOpen {z : ℂ | L.eval z ≠ 0} :=
    (isClosed_singleton (x := (0 : ℂ))).isOpen_compl.preimage L.continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (0 : ℂ) hL
  obtain ⟨σ, hσ⟩ := spectralPoint_eventually_small v hε
  exact ⟨σ, fun s hs => hball (by simpa only [Metric.mem_ball, dist_zero_right] using hσ s hs)⟩

/-- A fixed summable majorant for the difference from one on a right half-plane. -/
private theorem bound_unramified {n m : ℕ} (v : FinitePlace F)
    (a : Unramified.Eigenvalues n) (b : Unramified.Eigenvalues m) {A B : ℝ}
    (hA : ∀ x ∈ (a : Multiset ℂˣ), ‖(x : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ A)
    (hB : ∀ y ∈ (b : Multiset ℂˣ), ‖(y : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ B)
    {s : ℂ} (hs : A + B + ((n * m + 2 : ℕ) : ℝ) < s.re) :
    let x := RankinSelberg.spectralPoint (residueCardinality v) s
    let E := 2 ^ (n * m + 1) * (residueCardinality v : ℝ) ^ (-((n * m + 2 : ℕ) : ℝ))
    ‖((pairEulerPolynomial a b).eval x)⁻¹ - 1‖ ≤ E ∧ E ≤ 1 / 2 := by
  intro x E
  let q : ℝ := residueCardinality v
  let ε : ℝ := q ^ (-((n * m + 2 : ℕ) : ℝ))
  have hq2 : 2 ≤ q := by
    dsimp only [q]
    exact_mod_cast two_le_residueCardinality v
  have hq0 : 0 < q := by linarith
  have hab (α : ℂˣ) (hα : α ∈ (a : Multiset ℂˣ)) (β : ℂˣ) (hβ : β ∈ (b : Multiset ℂˣ)) :
      ‖(α : ℂ) * β * x‖ ≤ ε := by
    calc
      _ = ‖(α : ℂ)‖ * ‖(β : ℂ)‖ * q ^ (-s.re) := by
        rw [norm_mul, norm_mul, norm_spectralPoint]
      _ ≤ q ^ A * q ^ B * q ^ (-s.re) := by
        gcongr
        · exact hA α hα
        · exact hB β hβ
      _ = q ^ (A + B - s.re) := by rw [sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_add hq0]
      _ ≤ ε := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hε0 : 0 ≤ ε := Real.rpow_nonneg hq0.le _
  have hE : E ≤ 1 / 2 := by
    change 2 ^ (n * m + 1) * q ^ (-((n * m + 2 : ℕ) : ℝ)) ≤ _
    rw [Real.rpow_neg hq0.le, Real.rpow_natCast]
    calc
      _ ≤ 2 ^ (n * m + 1) * ((2 : ℝ) ^ (n * m + 2))⁻¹ := by gcongr
      _ = 1 / 2 := by
        rw [show n * m + 2 = (n * m + 1) + 1 from rfl, pow_succ _ (n * m + 1)]
        field_simp
  have hsmall : 2 ^ (n * m) * ε ≤ 1 / 2 := by
    apply le_trans _ hE
    change 2 ^ (n * m) * ε ≤ 2 ^ (n * m + 1) * ε
    apply mul_le_mul_of_nonneg_right _ hε0
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) (by norm_num)
  exact ⟨norm_inv_eval_pairEulerPolynomial_sub_one_le a b x hε0 hab hsmall, hE⟩

variable [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}

/-- The full finite Euler product is continuous on a sufficiently far right half-plane. -/
def RightHalfPlaneContinuous (c : FinitePairLChoice P P' h h') : Prop :=
  ∃ σ : ℝ, ContinuousOn (fun s => ∏' v, c.finiteL v s) {s : ℂ | σ < s.re}

/-- The uniform spherical majorant and the finite exceptional estimates give local uniform
convergence and continuity of the actual finite Euler product. -/
theorem rightHalfPlaneContinuous (c : FinitePairLChoice P P' h h') :
    c.RightHalfPlaneContinuous := by
  classical
  let S := P.exceptional ∪ P'.exceptional
  have hP : P.exceptional ⊆ S := Finset.subset_union_left
  have hP' : P'.exceptional ⊆ S := Finset.subset_union_right
  obtain ⟨A, hA⟩ := RankinSelbergGlobal.exists_hasSatakeBound_presentation T P
  obtain ⟨B, hB⟩ := RankinSelbergGlobal.exists_hasSatakeBound_presentation T' P'
  let d : ℕ := (r + 1) * (t + 1) + 2
  let E (v : FinitePlace F) : ℝ :=
    2 ^ ((r + 1) * (t + 1) + 1) * (residueCardinality v : ℝ) ^ (-(d : ℝ))
  have hsum : Summable E := by
    have hd : (1 : ℝ) < d := by exact_mod_cast (show 1 < d from by dsimp [d]; omega)
    simpa only [E, residueCardinality_eq_absNorm] using
      (HeckeEulerProduct.summable_absNorm_rpow (K := F) hd).mul_left
        (2 ^ ((r + 1) * (t + 1) + 1))
  have hlocal (v : FinitePlace F) (hv : v ∉ S) (s : ℂ) (hs : A + B + (d : ℝ) < s.re) :
      ‖c.finiteL v s - 1‖ ≤ E v ∧ E v ≤ 1 / 2 := by
    have hvP : v ∉ P.exceptional := fun hv' => hv (hP hv')
    have hvP' : v ∉ P'.exceptional := fun hv' => hv (hP' hv')
    have hpoly := isAutomorphicPairLPolynomial_eq_pairEulerPolynomial (padicField v)
      (c.additive v) (c.measure_spec v) _ _
      (hasSphericalSpectrum_padicObject P h v hvP)
      (hasSphericalSpectrum_padicObject P' h' v hvP') (c.lPolynomial_spec v)
    simpa only [finiteL, hpoly, E] using
      bound_unramified v _ _ (hA v hvP) (hB v hvP') hs
  have hL (v : FinitePlace F) : (c.lPolynomial v).eval 0 ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, hv⟩ := c.lPolynomial_spec v
    rw [← coeff_zero_eq_eval_zero, hv.coeff_zero]
    exact one_ne_zero
  choose σe hσe using (fun v : ↥(S : Set (FinitePlace F)) =>
    exists_exceptional_abscissa v.1 (c.lPolynomial v.1) (hL v.1))
  obtain ⟨σE, hσE⟩ := (Set.finite_range σe).bddAbove
  let σ := max (A + B + (d : ℝ)) σE
  let U : Set ℂ := {s | σ < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdenom (v : FinitePlace F) (s : ℂ) (hs : s ∈ U) :
      (c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s) ≠ 0 := by
    by_cases hv : v ∈ S
    · exact hσe ⟨v, hv⟩ s (lt_of_le_of_lt
        ((hσE (Set.mem_range_self ⟨v, hv⟩)).trans (le_max_right _ _)) hs)
    · intro hzero
      have hb := (hlocal v hv s (lt_of_le_of_lt (le_max_left _ _) hs)).1.trans
        (hlocal v hv s (lt_of_le_of_lt (le_max_left _ _) hs)).2
      simp only [finiteL, hzero, inv_zero, zero_sub, norm_neg, norm_one] at hb
      norm_num at hb
  have hc (v : FinitePlace F) : ContinuousOn (c.finiteL v) U := by
    have hq : (residueCardinality v : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (zero_lt_two.trans_le (two_le_residueCardinality v)))
    have hspec : Continuous (fun s => RankinSelberg.spectralPoint (residueCardinality v) s) :=
      continuous_neg.const_cpow (Or.inl hq)
    exact (((c.lPolynomial v).continuous.comp hspec).continuousOn).inv₀ (hdenom v)
  have hbd : ∀ᶠ v in cofinite, ∀ s ∈ U, ‖c.finiteL v s - 1‖ ≤ E v := by
    filter_upwards [S.eventually_cofinite_notMem] with v hv s hs
    exact (hlocal v hv s (lt_of_le_of_lt (le_max_left _ _) hs)).1
  have hprod := hsum.hasProdLocallyUniformlyOn_one_add hU hbd
    (fun v => (hc v).sub continuousOn_const)
  have hadd (z : ℂ) : 1 + (z - 1) = z := by ring
  have hprod' : HasProdLocallyUniformlyOn (fun v => c.finiteL v) (fun s => ∏' v, c.finiteL v s) U := by
    simpa only [hadd] using hprod
  refine ⟨σ, (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod').continuousOn ?_⟩
  exact (Eventually.of_forall fun I => continuousOn_finsetProd I fun v _ => hc v).frequently

end Langlands.Global.CuspidalPairPoles.FinitePairLChoice
