import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Classification.LanglandsData

/-!
# Epsilon factors through square-integrable Langlands data

Henniart 2002, Section 2.8: multiply the epsilon monomials of all pairs of
essentially square-integrable blocks. Existence of the block factors,
classification, and independence of the data remain explicit inputs.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

/-- The epsilon relation for arbitrary natural ranks, false at rank zero.
At positive ranks it uses the published larger-rank-first relation. -/
def IsPadicRankEpsilonFactor (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W)
    (e : ℂˣ × ℤ) : Prop :=
  match n, t, π, σ with
  | _ + 1, _ + 1, π, σ => IsPadicSymmetricEpsilonFactor F ψ ν π σ e
  | _, _, _, _ => False

section Rank

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isPadicRankEpsilonFactor_succ {r k : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (k + 1) F.Carrier) W} {e : ℂˣ × ℤ} :
    IsPadicRankEpsilonFactor F ψ ν π σ e ↔ IsPadicSymmetricEpsilonFactor F ψ ν π σ e :=
  Iff.rfl

/-- Uniqueness is inherited from the positive-rank epsilon relation. -/
theorem IsPadicRankEpsilonFactor.unique {n t : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W} {e e' : ℂˣ × ℤ}
    (h : IsPadicRankEpsilonFactor F ψ ν π σ e)
    (h' : IsPadicRankEpsilonFactor F ψ ν π σ e') : e = e' := by
  match n, t, π, σ, h, h' with
  | _ + 1, _ + 1, _, _, h, h' => exact IsPadicSymmetricEpsilonFactor.unique h h'

end Rank

/-- Product of epsilon monomials: multiply unit coefficients and add integer
exponents. This is not the usual componentwise multiplication of pairs. -/
def epsilonFactorProduct {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → κ → ℂˣ × ℤ) : ℂˣ × ℤ :=
  (∏ i, ∏ j, (e i j).1, ∑ i, ∑ j, (e i j).2)

private theorem epsilonMonomial_finset {ι : Type*} (a : Finset ι)
    (c : ι → ℂˣ) (m : ι → ℤ) {q : ℕ} (hq : 1 < q) (s : ℂ) :
    epsilonMonomial q (∏ i ∈ a, c i) (∑ i ∈ a, m i) s =
      ∏ i ∈ a, epsilonMonomial q (c i) (m i) s := by
  classical
  induction a using Finset.induction_on with
  | empty => simp [epsilonMonomial]
  | @insert i a hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    simp only [epsilonMonomial] at ih ⊢
    rw [Units.val_mul, zpow_add₀ (spectralPoint_ne_zero hq s), ← ih]
    ring

/-- The coefficient product and exponent sum evaluate to the product of the
original epsilon monomials, at every complex spectral parameter. -/
theorem epsilonMonomial_factorProduct {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → κ → ℂˣ × ℤ) {q : ℕ} (hq : 1 < q) (s : ℂ) :
    epsilonMonomial q (epsilonFactorProduct e).1 (epsilonFactorProduct e).2 s =
      ∏ i, ∏ j, epsilonMonomial q (e i j).1 (e i j).2 s := by
  change epsilonMonomial q (∏ i, ∏ j, (e i j).1) (∑ i, ∑ j, (e i j).2) s = _
  rw [epsilonMonomial_finset _ _ _ hq s]
  exact Finset.prod_congr rfl fun i _ => epsilonMonomial_finset _ _ _ hq s

section Data

variable (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {n t : ℕ}
  (d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData n)
  (d' : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData t)

/-- The prescribed epsilon factors of all pairs of square-integrable blocks exist. -/
def SquareIntegrableDataEpsilonExistence : Prop :=
  ∀ i j, ∃ e : ℂˣ × ℤ, letI := F.canonicalTopologicalData.topology
    IsPadicRankEpsilonFactor F ψ ν (d.blocks i).representation
      (d'.blocks j).representation e

/-- `e` is the product of epsilon factors of the block pairs of `d` and `d'`.
Each factor must satisfy the integral-based, positive-rank relation. -/
def IsSquareIntegrableDataEpsilonFactor (e : ℂˣ × ℤ) : Prop :=
  ∃ b : Fin d.shape.length → Fin d'.shape.length → ℂˣ × ℤ,
    (∀ i j, letI := F.canonicalTopologicalData.topology
      IsPadicRankEpsilonFactor F ψ ν (d.blocks i).representation
        (d'.blocks j).representation (b i j)) ∧ e = epsilonFactorProduct b

/-- Construct the product from existence of every block epsilon factor. -/
def squareIntegrableDataEpsilonFactor
    (h : SquareIntegrableDataEpsilonExistence F ψ ν d d') :
    {e : ℂˣ × ℤ // IsSquareIntegrableDataEpsilonFactor F ψ ν d d' e} :=
  ⟨epsilonFactorProduct (fun i j => Classical.choose (h i j)),
    ⟨_, (fun i j => Classical.choose_spec (h i j)), rfl⟩⟩

variable {F ψ ν d d'}

/-- For fixed data the product is unique, by uniqueness at each block pair. -/
theorem IsSquareIntegrableDataEpsilonFactor.unique {e e' : ℂˣ × ℤ}
    (h : IsSquareIntegrableDataEpsilonFactor F ψ ν d d' e)
    (h' : IsSquareIntegrableDataEpsilonFactor F ψ ν d d' e') : e = e' := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', rfl⟩ := h'
  have heq : b = b' := funext fun i => funext fun j => (hb i j).unique (hb' i j)
  rw [heq]

end Data

section Quotients

variable (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r t : ℕ}
  (π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
  (σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))

/-- The epsilon factor of an arbitrary irreducible pair through Langlands data.
Quotient data must exist for both representations, and every such pair of data
has block epsilon factors with the same product `e = (c,m)`, representing
`c q^(-ms)`. Both rank orders are allowed. -/
def IsLanglandsPairEpsilonFactor (e : ℂˣ × ℤ) : Prop :=
  (∃ d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1),
    d.IsLanglandsQuotient π) ∧
  (∃ d' : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData (t + 1),
    d'.IsLanglandsQuotient σ) ∧
  ∀ (d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1))
    (d' : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData (t + 1)),
    d.IsLanglandsQuotient π → d'.IsLanglandsQuotient σ →
      IsSquareIntegrableDataEpsilonFactor F ψ ν d d' e

/-- Explicit block-factor existence input for every datum pair presenting `π,σ`.
This proposition asserts no classification or independence theorem. -/
def LanglandsPairEpsilonBlockExistence : Prop :=
  ∀ (d : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1))
    (d' : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData (t + 1)),
    d.IsLanglandsQuotient π → d'.IsLanglandsQuotient σ →
      SquareIntegrableDataEpsilonExistence F ψ ν d d'

/-- Explicit independence input: all block products for data presenting the same
pair of representations agree. This is a proposition, not an assumed theorem. -/
def LanglandsPairEpsilonDataIndependence : Prop :=
  ∀ (d₁ d₂ : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData (r + 1))
    (d₁' d₂' : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData (t + 1)),
    d₁.IsLanglandsQuotient π → d₂.IsLanglandsQuotient π →
    d₁'.IsLanglandsQuotient σ → d₂'.IsLanglandsQuotient σ →
    ∀ e₁ e₂ : ℂˣ × ℤ,
      IsSquareIntegrableDataEpsilonFactor F ψ ν d₁ d₁' e₁ →
      IsSquareIntegrableDataEpsilonFactor F ψ ν d₂ d₂' e₂ → e₁ = e₂

/-- Construct the nongeneric epsilon factor from classification witnesses, block
factor existence, and datum independence. No arbitrary factor function is used. -/
def langlandsPairEpsilonFactor
    (hπ : ∃ d : SquareIntegrableLanglandsDatum.{uV, uF}
      F.canonicalTopologicalData (r + 1), d.IsLanglandsQuotient π)
    (hσ : ∃ d' : SquareIntegrableLanglandsDatum.{uW, uF}
      F.canonicalTopologicalData (t + 1), d'.IsLanglandsQuotient σ)
    (hb : LanglandsPairEpsilonBlockExistence.{uF, uV, uW} F ψ ν π σ)
    (hi : LanglandsPairEpsilonDataIndependence.{uF, uV, uW} F ψ ν π σ) :
    {e : ℂˣ × ℤ // IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e} := by
  let d := Classical.choose hπ
  let d' := Classical.choose hσ
  have hd : d.IsLanglandsQuotient π := Classical.choose_spec hπ
  have hd' : d'.IsLanglandsQuotient σ := Classical.choose_spec hσ
  let e := squareIntegrableDataEpsilonFactor F ψ ν d d' (hb d d' hd hd')
  refine ⟨e.val, hπ, hσ, ?_⟩
  intro a a' ha ha'
  let f := squareIntegrableDataEpsilonFactor F ψ ν a a' (hb a a' ha ha')
  have hef : e.val = f.val := hi d a d' a' hd ha hd' ha' e.val f.val e.property f.property
  exact hef ▸ f.property

variable {F ψ ν π σ}

/-- Uniqueness follows by selecting any quotient-data witnesses and applying
fixed-data product uniqueness. It needs no further independence hypothesis. -/
theorem IsLanglandsPairEpsilonFactor.unique {e e' : ℂˣ × ℤ}
    (h : IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e)
    (h' : IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e') : e = e' := by
  obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩, he⟩ := h
  exact (he d d' hd hd').unique (h'.2.2 d d' hd hd')

end Quotients

end Langlands.RankinSelberg
