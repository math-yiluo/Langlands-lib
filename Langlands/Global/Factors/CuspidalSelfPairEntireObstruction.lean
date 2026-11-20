import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Global.Factors.CuspidalPairResidueCardinality
import Langlands.Global.Factors.CuspidalSelfPairContinuationAssembly
import Langlands.Global.GlobalPlaceTopologyFacts

/-! # A cuspidal self-pair Euler product has no entire continuation -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalSelfPairAssembly

open NumberField CuspidalPairFunctionalEquation CuspidalPairBoundaryNonvanishing
open CuspidalPairAbsoluteConvergence
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T Td : CuspidalOperatorRealization F r}
  (hT : HasUnitaryCentralCharacter T) (hTd : Td.realization.IsContragredientOf T.realization)
  (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
  {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)

include hTd in
private theorem pairEulerPolynomial_eval_one_eq_zero (v : {v : FinitePlace F // v ∉ S}) :
    (pairEulerPolynomial (P.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP h)))
      (Pd.spectralSystem.eigenvalues v.1 (fun h => v.2 (hPd h)))).eval 1 = 0 := by
  let a := P.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP h))
  let b := Pd.spectralSystem.eigenvalues v.1 (fun h => v.2 (hPd h))
  have ha : (a : Multiset ℂˣ) ≠ 0 := by
    intro hzero
    have hc : (a : Multiset ℂˣ).card = r + 1 := Sym.card_coe
    rw [hzero, Multiset.card_zero] at hc
    exact (Nat.succ_ne_zero r) hc.symm
  obtain ⟨α, hα⟩ := Multiset.exists_mem_of_ne_zero ha
  have hb : α⁻¹ ∈ (b : Multiset ℂˣ) := by
    have heq := CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf
      T Td P Pd hTd v.1 (fun h => v.2 (hP h)) (fun h => v.2 (hPd h))
    change b = a.map (fun z => z⁻¹) at heq
    rw [heq]
    exact Multiset.mem_map.mpr ⟨α, hα, rfl⟩
  change (pairEulerPolynomial a b).eval 1 = 0
  rw [CuspidalPairEulerConvergence.eval_pairEulerPolynomial]
  apply Multiset.prod_eq_zero
  refine Multiset.mem_map.mpr ⟨(1 : ℂ), ?_, by simp⟩
  have hm : (α, α⁻¹) ∈ (a : Multiset ℂˣ) ×ˢ (b : Multiset ℂˣ) :=
    Multiset.mem_product.mpr ⟨hα, hb⟩
  exact Multiset.mem_map.mpr ⟨(α, α⁻¹), hm, by simp⟩

/-- The partial pair Euler product has no entire continuation from a right half-plane. -/
def NoEntireSelfPairContinuation : Prop :=
  ¬ ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    HasProd (fun v => partialEulerFactor P Pd hP hPd v s) (L s)

include hT in
private theorem selfPairLog_summableAt {a : ℝ} (ha : 2 < a) :
    GeneralDirichlet.SummableAt (selfCoeff P hP) logExponent a :=
  summable_of_le_geometric ha (sq_nonneg _) _
    (fun x => mul_nonneg (selfCoeff_nonneg P hP x) (Real.exp_pos _).le)
    (fun x => selfCoeff_mul_exp_le P hP (bound_P hT P hP) x a)

include hT hTd in
/-- On `2 < Re s`, the self-pair Euler product converges to the exponential of its log series. -/
theorem selfPair_hasProd_exp {s : ℂ} (hs : 2 < s.re) :
    HasProd (fun v => partialEulerFactor P Pd hP hPd v s)
      (Complex.exp (GeneralDirichlet.series (selfCoeff P hP) logExponent s)) := by
  have hlog : Summable (fun x : {v : FinitePlace F // v ∉ S} × ℕ =>
      ‖logEulerTerm P Pd hP hPd x.1 x.2 s‖) :=
    (selfPairLog_summableAt hT P hP hs).congr fun x => by
      rw [logEulerTerm_eq_term hT hTd P Pd hP hPd, GeneralDirichlet.norm_term,
        abs_of_nonneg (selfCoeff_nonneg P hP x)]
  obtain ⟨_, hp⟩ := summable_and_hasProd_of_summable P Pd hP hPd (bound_P hT P hP)
    (bound_Pd hT hTd P Pd hP hPd) (by linarith) hlog
  have he : (∑' x : {v : FinitePlace F // v ∉ S} × ℕ, logEulerTerm P Pd hP hPd x.1 x.2 s) =
      GeneralDirichlet.series (selfCoeff P hP) logExponent s :=
    tsum_congr fun x => logEulerTerm_eq_term hT hTd P Pd hP hPd x s
  rwa [he] at hp

set_option maxHeartbeats 600000 in
include hT hTd in
/-- The partial Euler product of a cuspidal realization with unitary central character
against a realization of its contragredient has no entire continuation. -/
theorem not_exists_entire_selfPair : NoEntireSelfPairContinuation P Pd hP hPd := by
  rintro ⟨L, hL, σ, hprod⟩
  have hLexp (s : ℂ) (hs : max σ 2 + 1 < s.re) :
      L s = Complex.exp (GeneralDirichlet.series (selfCoeff P hP) logExponent s) := by
    have hsσ : σ < s.re := by linarith [le_max_left σ 2]
    have hs2 : 2 < s.re := by linarith [le_max_right σ 2]
    exact (hprod s hsσ).unique (selfPair_hasProd_exp hT hTd P Pd hP hPd hs2)
  have hall := GeneralDirichlet.summableAt_of_exp (σ₀ := -1)
    (selfCoeff_nonneg P hP) (Real.log_pos one_lt_two) log_two_le_logExponent
    (selfPairLog_summableAt hT P hP (by linarith [le_max_right σ 2]))
    hL.differentiableOn hLexp
  let : Infinite (FinitePlace F) := numberField_finitePlaces_infinite F
  let : Infinite {v : FinitePlace F // v ∉ S} := (S.finite_toSet.infinite_compl).to_subtype
  let v : {v : FinitePlace F // v ∉ S} := Classical.choice inferInstance
  let c (k : ℕ) := selfCoeff P hP (v, k)
  let ℓ (k : ℕ) := logExponent (v, k)
  have hseries := GeneralDirichlet.differentiableOn_series (σc := -1)
    (fun k => logExponent_nonneg (v, k)) (fun k => selfCoeff_nonneg P hP (v, k))
    (fun a ha => (hall a ha).comp_injective (fun _ _ h => congrArg Prod.snd h))
  let A := pairEulerPolynomial (P.spectralSystem.eigenvalues v.1 (fun h => v.2 (hP h)))
    (Pd.spectralSystem.eigenvalues v.1 (fun h => v.2 (hPd h)))
  let D (s : ℂ) := A.eval (RankinSelberg.spectralPoint (residueCardinality v.1) s)
  have hD : Differentiable ℂ D := fun s =>
    (RankinSelberg.analyticAt_polynomial_spectralPoint (residueCardinality v.1)
      (FinitePairFactorChoice.one_lt_residueCardinality v.1) A s).differentiableAt
  have heq (s : ℂ) (hs : 1 < s.re) : D s * Complex.exp (GeneralDirichlet.series c ℓ s) = 1 := by
    obtain ⟨w, hw, he⟩ := exists_hasSum_logEulerTerm P Pd hP hPd (bound_P hT P hP)
      (bound_Pd hT hTd P Pd hP hPd) v hs
    have hw' : HasSum (fun k => GeneralDirichlet.term c ℓ k s) w :=
      hw.congr_fun fun k => (logEulerTerm_eq_term hT hTd P Pd hP hPd (v, k) s).symm
    change (D s)⁻¹ = Complex.exp w at he
    have hne : D s ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at he
      exact Complex.exp_ne_zero w he.symm
    rw [GeneralDirichlet.series, hw'.tsum_eq, ← he, mul_inv_cancel₀ hne]
  have hzero := GeneralDirichlet.eqOn_halfPlane (σc := -1)
    (hD.differentiableOn.mul hseries.cexp) (differentiableOn_const (1 : ℂ)) heq
    (by norm_num : -1 < (0 : ℂ).re)
  have hz : D 0 = 0 := by
    change A.eval (RankinSelberg.spectralPoint (residueCardinality v.1) 0) = 0
    simp only [RankinSelberg.spectralPoint, neg_zero, Complex.cpow_zero]
    exact pairEulerPolynomial_eval_one_eq_zero hTd P Pd hP hPd v
  change D 0 * Complex.exp (GeneralDirichlet.series c ℓ 0) = 1 at hzero
  rw [hz, zero_mul] at hzero
  exact zero_ne_one hzero

end Langlands.Global.CuspidalSelfPairAssembly
