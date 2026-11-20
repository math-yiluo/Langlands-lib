import Langlands.LocalFactor.RealPairLFactorNormalization
import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistLDivisibility

/-! # Symmetry of the completed pair data -/

noncomputable section

set_option autoImplicit false

universe u uQ uV uW

namespace Langlands.LocalFactor.Archimedean

private theorem list_prod_map_flatMap {α β : Type*} (f : β → ℂ) (g : α → List β) (xs : List α) :
    ((xs.flatMap g).map f).prod = (xs.map (fun x => ((g x).map f).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]

private theorem list_prod_map_eq_finprod {α : Type*} (xs : List α) (f : α → ℂ) :
    (xs.map f).prod = ∏ i : Fin xs.length, f (xs.get i) := by
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

private theorem complexPairLFactor_denominator_finprod (xs ys : List ComplexCharacterData) (s : ℂ) :
    (complexPairLFactor xs ys).denominator s =
      ∏ i : Fin xs.length, ∏ j : Fin ys.length, ((xs.get i).mul (ys.get j)).lFactor.denominator s := by
  rw [complexPairLFactor, complexPairBlocks, denominator_complexLFactor,
    list_prod_map_flatMap, list_prod_map_eq_finprod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [List.map_map, list_prod_map_eq_finprod]
    rfl

/-- The complex pair L-factor is symmetric in its two parameter lists. -/
theorem complexPairLFactor_comm (xs ys : List ComplexCharacterData) :
    complexPairLFactor xs ys = complexPairLFactor ys xs := by
  apply ReciprocalEntire.ext
  funext s
  rw [complexPairLFactor_denominator_finprod, complexPairLFactor_denominator_finprod, Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
  simp only [ComplexCharacterData.lFactor, ComplexCharacterData.mul, add_comm (xs.get i).weight,
    add_comm (xs.get i).exponent]

end Langlands.LocalFactor.Archimedean

namespace Langlands.RankinSelberg

open HarmonicAnalysis MeasureTheory Polynomial

/-- Interchanging the two actual smooth representations preserves their Langlands pair
L-polynomial. -/
theorem IsLanglandsPairLPolynomial.swap {p : ℕ} [Fact p.Prime]
    {K : PadicField.{u} p}
    {ψ : letI := K.canonicalTopologicalData.topology; UnitaryAdditiveCharacter K.Carrier}
    {ν : letI := K.canonicalTopologicalData.topology; letI := borel K.Carrier
      AdditiveHaarMeasure K.Carrier}
    {r t : ℕ}
    {π : letI := K.canonicalTopologicalData.topology
      SmoothRep.{0, u, max u uV} ℂ (GeneralLinear (r + 1) K.Carrier)}
    {σ : letI := K.canonicalTopologicalData.topology
      SmoothRep.{0, u, max u uW} ℂ (GeneralLinear (t + 1) K.Carrier)} {P : ℂ[X]}
    (h : IsLanglandsPairLPolynomial.{u, uV, uW} K ψ ν π σ P) :
    IsLanglandsPairLPolynomial.{u, uW, uV} K ψ ν σ π P := by
  exact ⟨h.2.1, h.1, fun e d he hd =>
    (Padic.isPadicSymmetricLPolynomial_comm K ψ ν _ _ P).mp (h.2.2 d e hd he)⟩

end Langlands.RankinSelberg

namespace Langlands.Correspondence

open Polynomial

/-- Interchanging the automorphic classes preserves a certified local pair polynomial. -/
theorem IsAutomorphicPairLPolynomial.swap {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}
    {r t : ℕ} {π : AutomorphicClass.{u, uV} K r.succPNat} {σ : AutomorphicClass.{u, uV} K t.succPNat}
    {ψ : NontrivialAdditiveCharacter K} {ν : LocalAdditiveHaarMeasure K} {P : ℂ[X]}
    (h : IsAutomorphicPairLPolynomial K ψ ν π σ P) : IsAutomorphicPairLPolynomial K ψ ν σ π P := by
  obtain ⟨A, B, J, J', hA, hB, hJ, hJ', hP⟩ := h
  exact ⟨B, A, J', J, hB, hA, hJ', hJ, hP.swap⟩

end Langlands.Correspondence

namespace Langlands.Global.CuspidalPairPoles

open NumberField LocalFactor.Archimedean
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F]

/-- The archimedean product is unchanged when the two parameter families are interchanged. -/
theorem archimedeanPairProduct_swap
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData) :
    archimedeanPairProduct dR' dR dC' dC = archimedeanPairProduct dR dR' dC dC' := by
  classical
  funext s
  unfold archimedeanPairProduct
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by rw [realPairLFactor_comm (dR' v) (dR v)]
  · exact Finset.prod_congr rfl fun v _ => by rw [complexPairLFactor_comm (dC' v) (dC v)]

namespace FinitePairLChoice

variable [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  (c : FinitePairLChoice P P' h h')

/-- Interchange the two presentations and retain the finite factors of the given choice. -/
def swap : FinitePairLChoice P' P h' h where
  additive := c.additive
  measure := c.measure
  measure_spec := c.measure_spec
  lPolynomial := c.lPolynomial
  lPolynomial_spec v := (c.lPolynomial_spec v).swap

@[simp]
theorem finiteL_swap (v : FinitePlace F) (s : ℂ) : c.swap.finiteL v s = c.finiteL v s := rfl

@[simp]
theorem isCompletedLFunction_swap (Linf Λ : ℂ → ℂ) :
    c.swap.IsCompletedLFunction Linf Λ ↔ c.IsCompletedLFunction Linf Λ := Iff.rfl

end FinitePairLChoice

end Langlands.Global.CuspidalPairPoles
