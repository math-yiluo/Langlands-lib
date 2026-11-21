import Langlands.Global.RankinSelberg.PartialEulerProductConvergence
import Langlands.Global.Factors.CuspidalPairEpsilonComparisonData
import Langlands.Representation.RankinSelberg.LanglandsLFactor

/-! # Nonvanishing of the finite factors on a common right half-plane -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace Langlands.BaseChange

open NumberField Global Global.CuspidalPairFunctionalEquation
open Global.CuspidalPairEulerConvergence Global.RankinSelbergGlobal
open Automorphic
open _root_.Polynomial

universe u uQ

variable {F : Type u} [Field F] [NumberField F]

private theorem exists_ne_zero_polynomial_eval_at_spectralPoint (v : Global.FinitePlace F)
    (P : ℂ[X]) (hP : P.coeff 0 = 1) :
    ∃ τ : ℝ, ∀ s : ℂ, τ < s.re →
      P.eval (RankinSelberg.spectralPoint (residueCardinality v) s) ≠ 0 := by
  let U : Set ℂ := {z | P.eval z ≠ 0}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage P.continuous
  have h0 : (0 : ℂ) ∈ U := by simp [U, ← coeff_zero_eq_eval_zero, hP]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  have hq1 : (1 : ℝ) < residueCardinality v := by exact_mod_cast two_le_residueCardinality v
  have hq0 : (0 : ℝ) < residueCardinality v := zero_lt_one.trans hq1
  have hlog := Real.log_pos hq1
  refine ⟨-Real.log ε / Real.log (residueCardinality v : ℝ), fun s hs => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, norm_spectralPoint, Real.rpow_def_of_pos hq0,
    ← Real.exp_log hε, Real.exp_lt_exp]
  have hlt := (div_lt_iff₀ hlog).mp hs
  linarith

variable [CompactSpace (AdeleQuotient F)]

private theorem exists_ne_zero_of_pairEulerOutside {r t : ℕ}
    {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (S : Finset (Global.FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (L : Global.FinitePlace F → ℂ[X]) (h0 : ∀ v, (L v).coeff 0 = 1)
    (hL : ∀ v (hv : v ∉ S), L v = pairEulerPolynomial
      (P.spectralSystem.eigenvalues v (fun h => hv (hP h)))
      (P'.spectralSystem.eigenvalues v (fun h => hv (hP' h)))) :
    ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → ∀ v,
      ((L v).eval (RankinSelberg.spectralPoint (residueCardinality v) s))⁻¹ ≠ 0 := by
  choose τ hτ using fun v => exists_ne_zero_polynomial_eval_at_spectralPoint v (L v) (h0 v)
  obtain ⟨M, hM⟩ := (S.finite_toSet.image τ).bddAbove
  obtain ⟨A, hA⟩ := exists_hasSatakeBound_presentation T P
  obtain ⟨B, hB⟩ := exists_hasSatakeBound_presentation T' P'
  refine ⟨max (A + B) M, fun s hs v => ?_⟩
  by_cases hv : v ∈ S
  · exact inv_ne_zero (hτ v s (lt_of_le_of_lt ((hM ⟨v, hv, rfl⟩).trans (le_max_right _ _)) hs))
  · rw [hL v hv, eval_pairEulerPolynomial]
    apply inv_ne_zero
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨x, hx, h0x⟩ := Multiset.mem_map.mp hzero
    obtain ⟨⟨α, β⟩, hab, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨hα, hβ⟩ := Multiset.mem_product.mp hab
    have hq1 : (1 : ℝ) < residueCardinality v := by exact_mod_cast two_le_residueCardinality v
    have hq0 : (0 : ℝ) < residueCardinality v := zero_lt_one.trans hq1
    have hsmall : ‖(α : ℂ) * β * RankinSelberg.spectralPoint (residueCardinality v) s‖ < 1 := by
      rw [norm_mul, norm_mul, norm_spectralPoint]
      calc
        _ ≤ (residueCardinality v : ℝ) ^ A * (residueCardinality v : ℝ) ^ B *
              (residueCardinality v : ℝ) ^ (-s.re) := by
          gcongr
          · exact hA v (fun h => hv (hP h)) α hα
          · exact hB v (fun h => hv (hP' h)) β hβ
        _ = (residueCardinality v : ℝ) ^ (A + B - s.re) := by
          rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, sub_eq_add_neg]
        _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1
          (sub_neg.mpr (lt_of_le_of_lt (le_max_left _ _) hs))
    have heq : (α : ℂ) * β * RankinSelberg.spectralPoint (residueCardinality v) s = 1 :=
      (sub_eq_zero.mp h0x).symm
    rw [heq, norm_one] at hsmall
    exact (lt_irrefl _ hsmall)

/-- The actual local factors of a cuspidal pair and its supplied dual pair
are nonzero on one common right half-plane. -/
def FinitePairFactorNonvanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T Td : CuspidalOperatorRealization F r) (T' Td' : CuspidalOperatorRealization F t),
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
      (P' : CuspidalSpectralPresentation.{u, uQ} T') (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
      (h : HasIrreducibleAdmissibleComponents P) (hd : HasIrreducibleAdmissibleComponents Pd)
      (h' : HasIrreducibleAdmissibleComponents P') (hd' : HasIrreducibleAdmissibleComponents Pd')
      (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd') (S : Finset (Global.FinitePlace F)),
      P.exceptional ⊆ S → Pd.exceptional ⊆ S → P'.exceptional ⊆ S → Pd'.exceptional ⊆ S →
      c.IsUnramifiedOutside S →
      ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → (∀ v, c.finiteL v s ≠ 0) ∧ (∀ v, c.finiteDualL v s ≠ 0)

theorem finitePairFactorNonvanishing : FinitePairFactorNonvanishingStatement.{u, uQ} := by
  intro F _ _ _ r t T Td T' Td' P Pd P' Pd' ψ h hd h' hd' c S hP hPd hP' hPd' hS
  obtain ⟨a, ha⟩ := exists_ne_zero_of_pairEulerOutside P P' S hP hP' c.lPolynomial
    (fun v => by
      obtain ⟨_, _, _, _, _, _, _, _, hpoly⟩ := c.lPolynomial_spec v
      exact hpoly.coeff_zero)
    (fun v hv => (hS v hv).1 (fun h => hv (hP h)) (fun h => hv (hP' h)))
  obtain ⟨b, hb⟩ := exists_ne_zero_of_pairEulerOutside Pd Pd' S hPd hPd' c.dualLPolynomial
    (fun v => by
      obtain ⟨_, _, _, _, _, _, _, _, hpoly⟩ := c.dualLPolynomial_spec v
      exact hpoly.coeff_zero)
    (fun v hv => (hS v hv).2.1 (fun h => hv (hPd h)) (fun h => hv (hPd' h)))
  exact ⟨max a b, fun s hs =>
    ⟨ha s (lt_of_le_of_lt (le_max_left a b) hs), hb s (lt_of_le_of_lt (le_max_right a b) hs)⟩⟩

open LocalFactor.Archimedean FunctionalEquationComparison.RelativeWeilEngine

/-- A completed pair equation with its unramified description gives the
functional-equation package used for products over base twists. -/
theorem hasGlobalEquation_of_completedPairEquation {r t : ℕ}
    {T Td : CuspidalOperatorRealization F r} {T' Td' : CuspidalOperatorRealization F t}
    {P : CuspidalSpectralPresentation.{u, uQ} T} {Pd : CuspidalSpectralPresentation.{u, uQ} Td}
    {P' : CuspidalSpectralPresentation.{u, uQ} T'} {Pd' : CuspidalSpectralPresentation.{u, uQ} Td'}
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    {h : HasIrreducibleAdmissibleComponents P} {hd : HasIrreducibleAdmissibleComponents Pd}
    {h' : HasIrreducibleAdmissibleComponents P'} {hd' : HasIrreducibleAdmissibleComponents Pd'}
    (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd') (S : Finset (Global.FinitePlace F))
    (hP : P.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPd' : Pd'.exceptional ⊆ S) (hS : c.IsUnramifiedOutside S)
    (A Ad : List GammaBlock) (Ae : ℂ → ℂ)
    (hEq : c.CompletedEquationHolds S (fun s => ((gammaProduct A).denominator s)⁻¹)
      (fun s => ((gammaProduct Ad).denominator s)⁻¹) Ae) :
    HasGlobalEquation c.finiteL c.finiteDualL c.finiteEpsilon
      (fun s => ((gammaProduct A).denominator s)⁻¹)
      (fun s => ((gammaProduct Ad).denominator s)⁻¹) Ae S :=
  c.hasGlobalEquation_of_completedEquation S A Ad Ae hEq
    (finitePairFactorNonvanishing F r t T Td T' Td' P Pd P' Pd' ψ h hd h' hd' c S
      hP hPd hP' hPd' hS)

end Langlands.BaseChange
