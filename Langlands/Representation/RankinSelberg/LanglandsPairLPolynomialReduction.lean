import Langlands.Representation.RankinSelberg.LanglandsLFactor
import Langlands.Representation.Classification.LanglandsDatumRealization

/-!
# Preserving a fixed L-polynomial through Langlands data

Regular-data uniqueness implies standard-module equivalence for data with
arbitrary block-carrier universes. One fixed standard-module L-polynomial then
certifies every tempered presentation of the same irreducible pair.
-/

noncomputable section

namespace Langlands.RankinSelberg

open CategoryTheory PadicField.TopologicalData MeasureTheory HarmonicAnalysis Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

section StandardModules

variable (F : PadicField.{uF} p) {r : ℕ}
  (π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier))

/-- Raising the blocks to the field universe lets regular-data uniqueness
compare standard modules without a saturation assumption on the input data. -/
theorem standardModule_equiv_of_regular_uniqueness
    (hcl : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (d e : TemperedLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData (r + 1))
    (hd : d.IsLanglandsQuotient π) (he : e.IsLanglandsQuotient π) :
    letI := F.canonicalTopologicalData.topology
    Nonempty (d.standardModule.representation.Equiv e.standardModule.representation) := by
  let := F.canonicalTopologicalData.topology
  let dL := d.universeLift.{uF, uV, uF}
  let eL := e.universeLift.{uF, uV, uF}
  have hdL : dL.IsLanglandsQuotient π :=
    (Classification.isIrreducibleQuotient_iff_of_equiv
      (d.universeLiftStandardModuleEquiv.{uF, uV, uF})).mp hd
  have heL : eL.IsLanglandsQuotient π :=
    (Classification.isIrreducibleQuotient_iff_of_equiv
      (e.universeLiftStandardModuleEquiv.{uF, uV, uF})).mp he
  obtain ⟨a⟩ := standardModule_iso_of_regular_uniqueness F π hcl dL eL hdL heL
  exact ⟨(d.universeLiftStandardModuleEquiv.{uF, uV, uF}).trans
    ((SmoothRep.equivOfIso a).trans
      (e.universeLiftStandardModuleEquiv.{uF, uV, uF}).symm)⟩

end StandardModules

section Certificate

variable (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r t : ℕ}
  (π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier))
  (σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier))

/-- Certify the supplied polynomial for every compatible tempered presentation,
retaining the original independent block-carrier universes. -/
theorem isLanglandsPairLPolynomial_of_standardModule
    (hclπ : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (hclσ : GLRegularLanglandsDataUniquenessStatement.{uF, uW})
    (d : TemperedLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1))
    (e : TemperedLanglandsDatum.{uW, uF} F.canonicalTopologicalData (t + 1))
    (hd : d.IsLanglandsQuotient π) (he : e.IsLanglandsQuotient σ)
    {P : ℂ[X]}
    (hP : letI := F.canonicalTopologicalData.topology
      IsPadicSymmetricLPolynomial F ψ ν d.standardModule.representation
        e.standardModule.representation P) :
    IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P := by
  let := F.canonicalTopologicalData.topology
  refine ⟨⟨d, hd⟩, ⟨e, he⟩, ?_⟩
  intro d' e' hd' he'
  obtain ⟨a⟩ := standardModule_equiv_of_regular_uniqueness F π hclπ d d' hd hd'
  obtain ⟨b⟩ := standardModule_equiv_of_regular_uniqueness F σ hclσ e e' he he'
  exact (IsPadicSymmetricLPolynomial.congr_equiv a b).mp hP

/-- A certificate on saturated data descends to the original block universes:
realize only the irreducible tempered blocks and preserve the supplied polynomial. -/
theorem isLanglandsPairLPolynomial_of_saturatedData
    (hclπ : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (hclσ : GLRegularLanglandsDataUniquenessStatement.{uF, uW})
    (d : TemperedLanglandsDatum.{max uF uV, uF}
      F.canonicalTopologicalData (r + 1))
    (e : TemperedLanglandsDatum.{max uF uW, uF}
      F.canonicalTopologicalData (t + 1))
    (hd : d.IsLanglandsQuotient π) (he : e.IsLanglandsQuotient σ)
    {P : ℂ[X]}
    (hP : letI := F.canonicalTopologicalData.topology
      IsPadicSymmetricLPolynomial F ψ ν d.standardModule.representation
        e.standardModule.representation P) :
    IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ P := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨d₀, _, _, ⟨a⟩⟩ := d.exists_realization.{uF, max uF uV, uV}
  obtain ⟨e₀, _, _, ⟨b⟩⟩ := e.exists_realization.{uF, max uF uW, uW}
  exact isLanglandsPairLPolynomial_of_standardModule F ψ ν π σ hclπ hclσ d₀ e₀
    ((Classification.isIrreducibleQuotient_iff_of_equiv a).mp hd)
    ((Classification.isIrreducibleQuotient_iff_of_equiv b).mp he)
    ((IsPadicSymmetricLPolynomial.congr_equiv a b).mp hP)

/-- Package the supplied polynomial and its descended Langlands certificate,
preserving its value definitionally. -/
def langlandsPairLPolynomialOfFixedSaturatedData
    (hclπ : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (hclσ : GLRegularLanglandsDataUniquenessStatement.{uF, uW})
    (d : TemperedLanglandsDatum.{max uF uV, uF}
      F.canonicalTopologicalData (r + 1))
    (e : TemperedLanglandsDatum.{max uF uW, uF}
      F.canonicalTopologicalData (t + 1))
    (hd : d.IsLanglandsQuotient π) (he : e.IsLanglandsQuotient σ)
    (P : ℂ[X])
    (hP : letI := F.canonicalTopologicalData.topology
      IsPadicSymmetricLPolynomial F ψ ν d.standardModule.representation
        e.standardModule.representation P) :
    {Q : ℂ[X] // IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν π σ Q} :=
  ⟨P, isLanglandsPairLPolynomial_of_saturatedData F ψ ν π σ
    hclπ hclσ d e hd he hP⟩

end Certificate

end Langlands.RankinSelberg
