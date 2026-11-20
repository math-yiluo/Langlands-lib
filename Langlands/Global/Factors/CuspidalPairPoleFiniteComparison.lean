import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.Representation.RankinSelberg.StableTwist.GammaCharacterChange

/-! # Independence of the finite pair L-data -/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ uV uW

namespace Langlands.RankinSelberg

open HarmonicAnalysis MeasureTheory

/-- A Langlands pair L-polynomial is independent of the choice of nontrivial
additive character and additive Haar measure. -/
theorem IsLanglandsPairLPolynomial.unique_of_data {p : ℕ} [Fact p.Prime]
    {K : PadicField.{u} p}
    {ψ χ : letI := K.canonicalTopologicalData.topology; UnitaryAdditiveCharacter K.Carrier}
    {ν μ : letI := K.canonicalTopologicalData.topology; letI := borel K.Carrier
      AdditiveHaarMeasure K.Carrier}
    {r t : ℕ}
    {π : letI := K.canonicalTopologicalData.topology
      SmoothRep.{0, u, max u uV} ℂ (GeneralLinear (r + 1) K.Carrier)}
    {σ : letI := K.canonicalTopologicalData.topology
      SmoothRep.{0, u, max u uW} ℂ (GeneralLinear (t + 1) K.Carrier)} {P Q : ℂ[X]}
    (hP : IsLanglandsPairLPolynomial.{u, uV, uW} K ψ ν π σ P)
    (hQ : IsLanglandsPairLPolynomial.{u, uV, uW} K χ μ π σ Q) : P = Q := by
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  let := K.canonicalTopologicalData.localField
  obtain ⟨a, ha⟩ := K.canonicalTopologicalData.exists_unit_scale_eq ψ χ
  obtain ⟨⟨d, hd⟩, ⟨e, he⟩, hP⟩ := hP
  have h := (Padic.isPadicSymmetricLPolynomial_characterChange K ψ a ν
    d.standardModule.representation e.standardModule.representation P).mp (hP d e hd he)
  rw [ha] at h
  exact h.unique_of_measure (hQ.2.2 d e hd he)

end Langlands.RankinSelberg

namespace Langlands.Correspondence

/-- Two certified L-polynomials of the same classes agree even when their
characters and measures differ. -/
theorem IsAutomorphicPairLPolynomial.unique_of_data {p : ℕ} [Fact p.Prime]
    {K : PadicField.{u} p} {r t : ℕ}
    {π : AutomorphicClass.{u, uV} K r.succPNat} {σ : AutomorphicClass.{u, uV} K t.succPNat}
    {ψ χ : NontrivialAdditiveCharacter K} {ν μ : LocalAdditiveHaarMeasure K} {P Q : ℂ[X]}
    (hP : IsAutomorphicPairLPolynomial K ψ ν π σ P)
    (hQ : IsAutomorphicPairLPolynomial K χ μ π σ Q) : P = Q := by
  obtain ⟨A, B, J, J', rfl, rfl, ⟨a⟩, ⟨b⟩, hP⟩ := hP
  exact hP.unique_of_data ((isAutomorphicPairLPolynomial_iff K A B J J' a b).mp hQ)

end Langlands.Correspondence

namespace Langlands.Global.CuspidalPairPoles.FinitePairLChoice

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T U : CuspidalOperatorRealization F r} {T' U' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {Q : CuspidalSpectralPresentation.{u, uQ} U} {Q' : CuspidalSpectralPresentation.{u, uQ} U'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {k : HasIrreducibleAdmissibleComponents Q} {k' : HasIrreducibleAdmissibleComponents Q'}

/-- Transport a finite pair L-choice to presentations with the same local classes. -/
def of_localClass_eq (c : FinitePairLChoice P P' h h')
    (hl : ∀ v, localClass P h v = localClass Q k v)
    (hr : ∀ v, localClass P' h' v = localClass Q' k' v) : FinitePairLChoice Q Q' k k' where
  additive := c.additive
  measure := c.measure
  measure_spec := c.measure_spec
  lPolynomial := c.lPolynomial
  lPolynomial_spec v := by
    rw [← hl v, ← hr v]
    exact c.lPolynomial_spec v

/-- The finite pair factor depends only on the two local classes at this place. -/
theorem finiteL_eq_of_localClass_eq (c : FinitePairLChoice P P' h h')
    (d : FinitePairLChoice Q Q' k k') (v : FinitePlace F)
    (hl : localClass P h v = localClass Q k v)
    (hr : localClass P' h' v = localClass Q' k' v) (s : ℂ) : c.finiteL v s = d.finiteL v s := by
  have hP := c.lPolynomial_spec v
  rw [hl, hr] at hP
  simp only [finiteL, hP.unique_of_data (d.lPolynomial_spec v)]

end Langlands.Global.CuspidalPairPoles.FinitePairLChoice
