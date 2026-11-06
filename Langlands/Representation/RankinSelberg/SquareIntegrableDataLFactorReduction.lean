import Langlands.Representation.RankinSelberg.GroupedLanglandsLFactor
import Langlands.Representation.RankinSelberg.LanglandsPairLPolynomialReduction

/-! # Reduction of the square-integrable-data L-factor formula -/

noncomputable section

namespace Langlands.RankinSelberg

open CategoryTheory MeasureTheory HarmonicAnalysis GeneralLinear Polynomial
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

section FixedField

variable (F : PadicField.{uF} p)

local instance reductionTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t : ℕ}
  (d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1))
  (e : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData (t + 1))
  (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (r + 1) F.Carrier))
  (σ : SmoothRep.{0, uF, max uF uW} ℂ (GeneralLinear (t + 1) F.Carrier))

/-- Group lifted square-integrable data, compute the grouped product, and
preserve its exact polynomial in the original-universe Langlands certificate. -/
theorem squareIntegrableDataLFactor_of_grouping
    (HGd : Classification.SquareIntegrableEqualExponentGrouping.{uF, uV}
      F F.canonicalTopologicalData)
    (HGe : Classification.SquareIntegrableEqualExponentGrouping.{uF, uW}
      F F.canonicalTopologicalData)
    (HT : TemperedLFactorStatement.{uF, max uF uV, max uF uW})
    (HL : LanglandsTypeLFactorStatement.{uF, max uF uV, max uF uW})
    (hclπ : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (hclσ : GLRegularLanglandsDataUniquenessStatement.{uF, uW})
    (hd : d.IsLanglandsQuotient π) (he : e.IsLanglandsQuotient σ) :
    ∃ (P : ℂ[X]) (Q : Fin d.shape.length → Fin e.shape.length → ℂ[X]),
      IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π σ P ∧
      (∀ i j, IsPadicRankLPolynomial F ψ ν.val
        (d.blocks i).representation (e.blocks j).representation (Q i j)) ∧
      P = ∏ i, ∏ j, Q i j := by
  classical
  let dL := d.universeLift.{uF, uV, uF}
  let eL := e.universeLift.{uF, uW, uF}
  let g := squareIntegrableFactorGrouping F HGd (Nat.succ_pos r) dL
  let h := squareIntegrableFactorGrouping F HGe (Nat.succ_pos t) eL
  have hdL : dL.IsLanglandsQuotient π :=
    (Classification.isIrreducibleQuotient_iff_of_equiv
      (d.universeLiftInducedEquiv.{uF, uV, uF})).mp hd
  have heL : eL.IsLanglandsQuotient σ :=
    (Classification.isIrreducibleQuotient_iff_of_equiv
      (e.universeLiftInducedEquiv.{uF, uW, uF})).mp he
  obtain ⟨ag⟩ := g.inducedIso
  obtain ⟨ah⟩ := h.inducedIso
  have hgt : g.tempered.IsLanglandsQuotient π :=
    (Classification.isIrreducibleQuotient_iff_of_equiv (SmoothRep.equivOfIso ag)).mp hdL
  have hht : h.tempered.IsLanglandsQuotient σ :=
    (Classification.isIrreducibleQuotient_iff_of_equiv (SmoothRep.equivOfIso ah)).mp heL
  obtain ⟨P, Q, hP, hQ, hprod⟩ := g.product F ψ ν h HT HL
  refine ⟨P, Q, ?_, ?_, hprod⟩
  · exact isLanglandsPairLPolynomial_of_saturatedData F ψ ν.val π σ
      hclπ hclσ g.tempered h.tempered hgt hht hP
  · intro i j
    exact (IsPadicRankLPolynomial.congr_equiv
      (SmoothRep.universeLiftEquiv.{uF} (d.blocks i))
      (SmoothRep.universeLiftEquiv.{uF} (e.blocks j))).mpr (hQ i j)

/-- Choose the polynomial and all block-pair polynomials together with their
original-universe certificates and exact product identity. -/
def squareIntegrableDataLFactorPolynomials
    (HGd : Classification.SquareIntegrableEqualExponentGrouping.{uF, uV}
      F F.canonicalTopologicalData)
    (HGe : Classification.SquareIntegrableEqualExponentGrouping.{uF, uW}
      F F.canonicalTopologicalData)
    (HT : TemperedLFactorStatement.{uF, max uF uV, max uF uW})
    (HL : LanglandsTypeLFactorStatement.{uF, max uF uV, max uF uW})
    (hclπ : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (hclσ : GLRegularLanglandsDataUniquenessStatement.{uF, uW})
    (hd : d.IsLanglandsQuotient π) (he : e.IsLanglandsQuotient σ) :
    {PQ : ℂ[X] × (Fin d.shape.length → Fin e.shape.length → ℂ[X]) //
      IsLanglandsPairLPolynomial.{uF, uV, uW} F ψ ν.val π σ PQ.1 ∧
      (∀ i j, IsPadicRankLPolynomial F ψ ν.val
        (d.blocks i).representation (e.blocks j).representation (PQ.2 i j)) ∧
      PQ.1 = ∏ i, ∏ j, PQ.2 i j} :=
  let h := squareIntegrableDataLFactor_of_grouping F ψ ν d e π σ
    HGd HGe HT HL hclπ hclσ hd he
  ⟨(h.choose, h.choose_spec.choose), h.choose_spec.choose_spec⟩

end FixedField

/-- The exact existing square-integrable-data statement follows from the
analytic formulas, actual grouping, and regular-data uniqueness. -/
theorem squareIntegrableDataLFactor_of_prerequisites
    (HGd : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      Classification.SquareIntegrableEqualExponentGrouping.{uF, uV}
        F F.canonicalTopologicalData)
    (HGe : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      Classification.SquareIntegrableEqualExponentGrouping.{uF, uW}
        F F.canonicalTopologicalData)
    (HT : TemperedLFactorStatement.{uF, max uF uV, max uF uW})
    (HL : LanglandsTypeLFactorStatement.{uF, max uF uV, max uF uW})
    (hclπ : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    (hclσ : GLRegularLanglandsDataUniquenessStatement.{uF, uW}) :
    SquareIntegrableDataLFactorStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t d e π σ hd he
  exact squareIntegrableDataLFactor_of_grouping F ψ ν d e π σ
    (HGd p F) (HGe p F) HT HL hclπ hclσ hd he

end Langlands.RankinSelberg
