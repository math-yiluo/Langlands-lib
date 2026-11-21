import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Global.Factors.CuspidalFinitePairRegularityProof
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Global.Factors.CuspidalPairPoleFiniteEuler
import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.Global.Factors.CuspidalPairResidueCardinality
import Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof
import Langlands.Global.Factors.RelativeWeilEngine
import Mathlib.Analysis.Meromorphic.NormalForm

/-! # Entire continuation of the nondual partial Euler product -/

noncomputable section

set_option autoImplicit false

universe u uQ

open scoped Topology

namespace Langlands.Global

open NumberField Automorphic CuspidalPairPoles CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing Filter LocalFactor.Archimedean
open FunctionalEquationComparison.CompletedEquationAdapter
  (realPairLFactor_denominator_ne_zero complexPairLFactor_denominator_ne_zero
    prod_inv_denominator_ne_zero)

/-- An equal-rank cuspidal pair with trivial split-centre actions and outside the
contragredient case has an entire partial Euler product. -/
def CuspidalNondualPartialEulerContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T T' : CuspidalOperatorRealization F r),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
    ∀ (P : CuspidalSpectralPresentation.{u,uQ} T)
      (P' : CuspidalSpectralPresentation.{u,uQ} T'),
      HasIrreducibleAdmissibleComponents P → HasIrreducibleAdmissibleComponents P' →
      ¬ T.realization.IsContragredientOf T'.realization →
      ∀ (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S) (hP'S : P'.exceptional ⊆ S),
        ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
          HasProd (fun v : {v // v ∉ S} => partialEulerFactor P P' hPS hP'S v s) (L s)

private theorem meromorphic_of_poleProfile {Λ : ℂ → ℂ} {cond : Prop}
    (h : HasSimplePoleProfile Λ cond) : Meromorphic Λ := by
  intro z
  by_cases hz : z ∈ ({0, 1} : Set ℂ)
  · exact (h.2 z hz).1
  · have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
      ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
    exact (h.1.analyticAt (hopen.mem_nhds hz)).meromorphicAt

private theorem entire_of_nondual {Λ : ℂ → ℂ} {cond : Prop}
    (h : HasSimplePoleProfile Λ cond) (hn : ¬ cond) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ Set.EqOn L Λ ({0, 1} : Set ℂ)ᶜ := by
  have hm : MeromorphicOn Λ Set.univ := fun z _ => meromorphic_of_poleProfile h z
  let L := toMeromorphicNFOn Λ Set.univ
  have heq (z : ℂ) (hz : z ∉ ({0, 1} : Set ℂ)) : L =ᶠ[𝓝 z] Λ := by
    have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
      ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
    have ha := h.1.analyticAt (hopen.mem_nhds hz)
    simpa only [toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt] using
      toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hm (Set.mem_univ z)
  refine ⟨L, fun z => ?_, fun z hz => (heq z hz).eq_of_nhds⟩
  by_cases hz : z ∈ ({0, 1} : Set ℂ)
  · have hnf := meromorphicNFOn_toMeromorphicNFOn Λ Set.univ (Set.mem_univ z)
    apply (hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_).differentiableAt
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (Set.mem_univ z)]
    exact le_of_not_gt fun hp => hn ((h.2 z hz).2.2.mp hp)
  · have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
      ((Set.finite_singleton (1 : ℂ)).insert 0).isClosed.isOpen_compl
    exact ((h.1.analyticAt (hopen.mem_nhds hz)).congr (heq z hz).symm).differentiableAt

private theorem cleared_hasProd {Q I J : Type*} [Fintype I] [Fintype J]
    {f : Q → ℂ} {R : I → ℂ} {C : J → ℂ} {p z : ℂ}
    (S : Finset Q) (hp : HasProd (fun v => (f v)⁻¹) p)
    (hz : z = ((∏ i, (R i)⁻¹) * ∏ j, (C j)⁻¹) * p)
    (hf : ∀ v ∈ S, f v ≠ 0) (hR : ∀ i, R i ≠ 0) (hC : ∀ j, C j ≠ 0) :
    HasProd (fun v : {v // v ∉ S} => (f v)⁻¹)
      (((∏ v ∈ S, f v) * ((∏ i, R i) * ∏ j, C j)) * z) := by
  classical
  have hprod := FunctionalEquationComparison.RelativeWeilEngine.hasProd_compl_of_ne_zero hp S
    (fun v hv => inv_ne_zero (hf v hv))
  rw [Finset.prod_inv_distrib, inv_inv] at hprod
  have hRC : ((∏ i, R i) * ∏ j, C j) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hR i)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hC j)
  have hz' : ((∏ i, R i) * ∏ j, C j) * z = p := by
    rw [hz, Finset.prod_inv_distrib, Finset.prod_inv_distrib, ← mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hRC, one_mul]
  rw [mul_assoc, hz', mul_comm]
  exact hprod

set_option maxHeartbeats 1400000 in
/-- An equal-rank completion with no poles gives entire continuation of the
product outside any finite set containing both exceptional sets. -/
theorem partialEulerContinuation_of_nondual_completion
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    {T T' : CuspidalOperatorRealization F r}
    {P : CuspidalSpectralPresentation.{u,uQ} T} {P' : CuspidalSpectralPresentation.{u,uQ} T'}
    {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    {Λ : ℂ → ℂ} {cond : Prop} (hΛ : c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ)
    (hprof : HasSimplePoleProfile Λ cond) (hn : ¬ cond)
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S) (hP'S : P'.exceptional ⊆ S) :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      HasProd (fun v : {v // v ∉ S} => partialEulerFactor P P' hPS hP'S v s) (L s) := by
  classical
  obtain ⟨σ, hprod⟩ := hΛ
  obtain ⟨Λ₀, hΛ₀, heqΛ⟩ := entire_of_nondual hprof hn
  let f (v : FinitePlace F) (s : ℂ) :=
    (c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s)
  let R (v : {v : InfinitePlace F // v.IsReal}) := realPairLFactor (dR v) (dR' v)
  let C (v : {v : InfinitePlace F // v.IsComplex}) := complexPairLFactor (dC v) (dC' v)
  let A (s : ℂ) := (∏ v ∈ S, f v s) * ((∏ v, (R v).denominator s) * ∏ v, (C v).denominator s)
  have hA : Differentiable ℂ A := by
    refine Differentiable.mul (Differentiable.fun_finsetProd fun v _ s => ?_)
      ((Differentiable.fun_finsetProd fun v _ => (R v).entire).mul
        (Differentiable.fun_finsetProd fun v _ => (C v).entire))
    exact (RankinSelberg.analyticAt_polynomial_spectralPoint (residueCardinality v)
      (FinitePairFactorChoice.one_lt_residueCardinality v) (c.lPolynomial v) s).differentiableAt
  have hunit := cuspidalSplitCentreUnitaryCentralCharacter F r T hT
  have hunit' := cuspidalSplitCentreUnitaryCentralCharacter F r T' hT'
  obtain ⟨σR, hσR⟩ := prod_inv_denominator_ne_zero R
    (fun v => realPairLFactor_denominator_ne_zero (dR v) (dR' v))
  obtain ⟨σC, hσC⟩ := prod_inv_denominator_ne_zero C
    (fun v => complexPairLFactor_denominator_ne_zero (dC v) (dC' v))
  refine ⟨A * Λ₀, hA.mul hΛ₀, max (max 1 σ) (max σR σC), fun s hs => ?_⟩
  have hs₁ := ((le_max_left 1 σ).trans (le_max_left _ _)).trans_lt hs
  have hsσ := ((le_max_right 1 σ).trans (le_max_left _ _)).trans_lt hs
  have hsR := ((le_max_left σR σC).trans (le_max_right _ _)).trans_lt hs
  have hsC := ((le_max_right σR σC).trans (le_max_right _ _)).trans_lt hs
  have hreg : s ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl) <;> norm_num at hs₁
  have hf (v : FinitePlace F) : f v s ≠ 0 :=
    cuspidalFinitePairRegularity F r r T T' hunit hunit' P P' h h' c v s hs₁.le
  have hRne (v : {v : InfinitePlace F // v.IsReal}) : (R v).denominator s ≠ 0 := by
    simpa using Finset.prod_ne_zero_iff.mp (hσR s hsR) v (Finset.mem_univ v)
  have hCne (v : {v : InfinitePlace F // v.IsComplex}) : (C v).denominator s ≠ 0 := by
    simpa using Finset.prod_ne_zero_iff.mp (hσC s hsC) v (Finset.mem_univ v)
  have heuler (v : {v : FinitePlace F // v ∉ S}) :
      (f v s)⁻¹ = partialEulerFactor P P' hPS hP'S v s :=
    c.finiteL_eq_partialEulerFactor hPS hP'S v s
  obtain ⟨_, p, hp, he⟩ := hprod s hsσ
  change HasProd _ (A s * Λ₀ s)
  rw [heqΛ hreg, ← funext heuler]
  exact cleared_hasProd S hp he (fun v _ => hf v) hRne hCne

set_option maxHeartbeats 1400000 in
/-- Clearing the omitted local denominators of the entire nondual completion
continues the equal-rank partial Euler product. -/
theorem cuspidalNondualPartialEulerContinuation_of_pairPole
    (hpole : CuspidalPairPoleStatement.{u,uQ}) :
    CuspidalNondualPartialEulerContinuationStatement.{u,uQ} := by
  intro F _ _ _ r T T' hT hT' P P' h h' hn S hPS hP'S
  obtain ⟨⟨⟨c⟩, hR, hC⟩, hΛ⟩ := hpole F r r T T' hT hT' P P' h h'
  choose dR hdR using fun v => (hR v).1
  choose dR' hdR' using fun v => (hR v).2
  choose dC hdC using fun v => (hC v).1
  choose dC' hdC' using fun v => (hC v).2
  obtain ⟨Λ, hprod, hprof, _⟩ := hΛ c dR dR' hdR hdR' dC dC' hdC hdC'
  refine partialEulerContinuation_of_nondual_completion hT hT' c dR dR' dC dC'
    hprod hprof ?_ S hPS hP'S
  rintro ⟨hrt, hcontr⟩
  cases Subsingleton.elim hrt rfl
  exact hn hcontr

end Langlands.Global
