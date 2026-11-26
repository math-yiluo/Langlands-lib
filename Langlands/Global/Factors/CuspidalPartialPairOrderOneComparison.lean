import Langlands.Automorphic.CuspidalArchimedeanComponentStatement
import Langlands.Automorphic.CuspidalArchimedeanPairRegularityProof
import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Global.Factors.CuspidalFinitePairRegularityProof
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingReduction
import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Global.Factors.CuspidalPairResidueCardinality
import Langlands.Global.Factors.MeromorphicPoleComparisonProof

/-! # Order transfer from a shifted completed cuspidal pair L-function -/

noncomputable section

set_option autoImplicit false

universe u uQ uA

namespace Langlands.Global.CuspidalPartialPairOrderOne

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CuspidalPairBoundaryNonvanishing (IsPartialPairLFunction partialEulerFactor)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents residueCardinality)
open CuspidalPairFunctionalEquation.FinitePairFactorChoice (one_lt_residueCardinality)
open CuspidalPairPoles PoleComparison
open LocalFactor (ReciprocalEntire)
open LocalFactor.Archimedean
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Comparing the Euler factors after an imaginary shift identifies the order of the
supplied partial L-function at `1` with the completed order at `1 + d`. -/
theorem completedOrder_eq {r t : ℕ}
    {T U : CuspidalOperatorRealization F r} {T' U' : CuspidalOperatorRealization F t}
    {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
    {S : Finset (FinitePlace F)} {hP : P.exceptional ⊆ S} {hP' : P'.exceptional ⊆ S}
    {L : ℂ → ℂ}
    {Q : CuspidalSpectralPresentation.{u, uA} U} {Q' : CuspidalSpectralPresentation.{u, uA} U'}
    {hQ : HasIrreducibleAdmissibleComponents Q} {hQ' : HasIrreducibleAdmissibleComponents Q'}
    (c : FinitePairLChoice Q Q' hQ hQ')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (hdR : ∀ v, OperatorRealization.HasRealPlaceParameter U.realization v (dR v))
    (hdR' : ∀ v, OperatorRealization.HasRealPlaceParameter U'.realization v (dR' v))
    (hdC : ∀ v, OperatorRealization.HasComplexPlaceParameter U.realization v (dC v))
    (hdC' : ∀ v, OperatorRealization.HasComplexPlaceParameter U'.realization v (dC' v))
    (hU : HasUnitaryCentralCharacter U) (hU' : HasUnitaryCentralCharacter U')
    (hL : IsPartialPairLFunction P P' hP hP' L) {Λ : ℂ → ℂ} {d : ℂ}
    (hΛ : MeromorphicOn Λ Set.univ)
    (hΛprod : c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ)
    (hd : d.re = 0)
    (hmatch : ∀ (v : {v : FinitePlace F // v ∉ S}) s,
      c.finiteL v.1 (s + d) = partialEulerFactor P P' hP hP' v s) :
    meromorphicOrderAt L 1 = meromorphicOrderAt Λ (1 + d) := by
  classical
  let realD (v : {v : InfinitePlace F // v.IsReal}) := realPairLFactor (dR v) (dR' v)
  let complexD (v : {v : InfinitePlace F // v.IsComplex}) := complexPairLFactor (dC v) (dC' v)
  let boundary (s : ℂ) := archimedeanPairProduct dR dR' dC dC' (s + d)
  let finiteL (v : FinitePlace F) (s : ℂ) := c.finiteL v (s + d)
  have htranslate (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => z + d) s :=
    analyticAt_id.add analyticAt_const
  have harchDenom (D : ReciprocalEntire) (s : ℂ) :
      AnalyticAt ℂ (fun z => D.denominator (z + d)) s :=
    (D.entire.analyticAt (s + d)).comp (f := (· + d)) (htranslate s)
  have hfiniteDenom (v : FinitePlace F) (s : ℂ) : AnalyticAt ℂ
      (fun z => (c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) (z + d)))
      s :=
    (RankinSelberg.analyticAt_polynomial_spectralPoint _ (one_lt_residueCardinality v)
      (c.lPolynomial v) (s + d)).comp (f := (· + d)) (htranslate s)
  have hboundaryMeromorphic : Meromorphic boundary := by
    intro s
    exact (MeromorphicAt.fun_prod (fun v _ => (harchDenom (realD v) s).meromorphicAt.inv)).mul
      (MeromorphicAt.fun_prod (fun v _ => (harchDenom (complexD v) s).meromorphicAt.inv))
  have homittedMeromorphic : Meromorphic (omittedProduct S finiteL) := fun s =>
    MeromorphicAt.fun_prod (fun v _ => (hfiniteDenom v s).meromorphicAt.inv)
  have hproduct : Meromorphic (completedProduct S L finiteL boundary) :=
    hboundaryMeromorphic.mul (homittedMeromorphic.mul hL.meromorphic)
  have hre (s : ℂ) : (s + d).re = s.re := by simp [Complex.add_re, hd]
  obtain ⟨σ, hσ⟩ := hΛprod
  obtain ⟨τ, hτ⟩ := hL.2
  have hΛshift : Meromorphic (fun s => Λ (s + d)) :=
    Meromorphic.meromorphic_fun_comp_add_const_iff_meromorphic.mpr (meromorphicOn_univ.mp hΛ)
  have hgerm := FunctionalEquationComparison.eq_on_halfplane_meromorphicEq
    (σ := max σ τ) hΛshift hproduct (fun s hs => by
      obtain ⟨-, p, hp, hΛs⟩ := hσ (s + d) (by
        rw [hre]
        exact (le_max_left σ τ).trans_lt hs)
      have htail : HasProd (fun v : {v : FinitePlace F // v ∉ S} => finiteL v.1 s) (L s) :=
        (hτ s ((le_max_right σ τ).trans_lt hs)).2.congr_fun (fun v => hmatch v s)
      have hall := (S.hasProd (fun v => finiteL v s)).mul_compl htail
      change Λ (s + d) = _
      rw [hΛs, hp.unique hall]
      rfl)
  have hreOne : 1 ≤ (1 + d).re := by rw [hre, Complex.one_re]
  have homitted : OmittedUnitsAt S finiteL 1 := by
    intro v _
    have hne := cuspidalFinitePairRegularity F r t U U' hU hU' Q Q' hQ hQ' c v (1 + d) hreOne
    exact ⟨(hfiniteDenom v 1).inv hne, inv_ne_zero hne⟩
  obtain ⟨hreal, hcomplex⟩ := Automorphic.cuspidalArchimedeanPairRegularity F r t U U' hU hU'
  have hrealUnit := omittedProduct_holomorphicUnitAt Finset.univ
    (fun v s => ((realD v).denominator (s + d))⁻¹) 1 (fun v _ => by
      have hne := hreal v (dR v) (dR' v) (hdR v) (hdR' v) (1 + d) hreOne
      exact ⟨(harchDenom (realD v) 1).inv hne, inv_ne_zero hne⟩)
  have hcomplexUnit := omittedProduct_holomorphicUnitAt Finset.univ
    (fun v s => ((complexD v).denominator (s + d))⁻¹) 1 (fun v _ => by
      have hne := hcomplex v (dC v) (dC' v) (hdC v) (hdC' v) (1 + d) hreOne
      exact ⟨(harchDenom (complexD v) 1).inv hne, inv_ne_zero hne⟩)
  have hboundary : HolomorphicUnitAt boundary 1 :=
    ⟨hrealUnit.1.fun_mul hcomplexUnit.1, mul_ne_zero hrealUnit.2 hcomplexUnit.2⟩
  calc
    meromorphicOrderAt L 1 =
        meromorphicOrderAt (completedProduct S L finiteL boundary) 1 :=
      (finiteOmittedOrder _ S L finiteL boundary 1 homitted hboundary).symm
    _ = meromorphicOrderAt (fun s => Λ (s + d)) 1 :=
      meromorphicOrderAt_congr (hgerm 1).symm
    _ = meromorphicOrderAt Λ (1 + d) :=
      meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt

end Langlands.Global.CuspidalPartialPairOrderOne
