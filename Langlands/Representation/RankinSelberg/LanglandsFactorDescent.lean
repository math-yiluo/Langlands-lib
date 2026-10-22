import Langlands.Representation.RankinSelberg.LanglandsFactors
import Langlands.Representation.Classification.MultisegmentClassificationStatement

/-!
# Epsilon products and the square-integrable classification

Derive datum independence from block isomorphisms and permutations, then construct
the epsilon factor using the published classification and exhaustion propositions.
Classification and block-factor existence remain explicit hypotheses.
-/

noncomputable section

namespace Langlands.RankinSelberg

open CategoryTheory MeasureTheory HarmonicAnalysis PadicField.TopologicalData

universe uF uV uW uV' uW'

variable {p : ℕ} [Fact p.Prime]

section Invariance

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}

/-- The natural-rank adapter preserves the underlying epsilon relation's
invariance under representation equivalence, including its false zero cases. -/
theorem IsPadicRankEpsilonFactor.congr_equiv
    {n t : ℕ} {V : Type uV} {W : Type uW} {V' : Type uV'} {W' : Type uW'}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W}
    {π' : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V'}
    {σ' : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W'}
    (φ : π.Equiv π') (φ' : σ.Equiv σ') {e : ℂˣ × ℤ} :
    IsPadicRankEpsilonFactor F ψ ν π σ e ↔
      IsPadicRankEpsilonFactor F ψ ν π' σ' e := by
  cases n with
  | zero => rfl
  | succ n =>
    cases t with
    | zero => rfl
    | succ t => exact IsPadicSymmetricEpsilonFactor.congr_equiv φ φ'

private theorem rankEpsilonFactor_congr_iso
    {n n' t t' : ℕ} (hn : n = n') (ht : t = t')
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n F.Carrier))
    (B : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear t F.Carrier))
    (A' : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uV} ℂ (Langlands.GeneralLinear n' F.Carrier))
    (B' : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear t' F.Carrier))
    (φ : (hn ▸ A) ≅ A') (φ' : (ht ▸ B) ≅ B') {e : ℂˣ × ℤ} :
    letI := F.canonicalTopologicalData.topology
    IsPadicRankEpsilonFactor F ψ ν A.representation B.representation e ↔
      IsPadicRankEpsilonFactor F ψ ν A'.representation B'.representation e := by
  cases hn
  cases ht
  let := F.canonicalTopologicalData.topology
  exact IsPadicRankEpsilonFactor.congr_equiv
    (SmoothRep.equivOfIso φ) (SmoothRep.equivOfIso φ')

/-- Reindexing either finite block family preserves the product of monomials. -/
theorem epsilonFactorProduct_reindex
    {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e : ι ≃ ι') (f : κ ≃ κ') (b : ι' → κ' → ℂˣ × ℤ) :
    epsilonFactorProduct (fun i j => b (e i) (f j)) = epsilonFactorProduct b := by
  apply Prod.ext
  · exact Fintype.prod_equiv e _ _ fun i => f.prod_comp (fun j => (b (e i) j).1)
  · exact Fintype.sum_equiv e _ _ fun i => f.sum_comp (fun j => (b (e i) j).2)

/-- Two certified products agree whenever the block families match by
permutations, rank equalities and actual isomorphisms. No analytic existence or
classification theorem is needed for this conditional comparison. -/
theorem squareIntegrableDataEpsilonFactor_eq_of_matching
    {n t : ℕ}
    (d₁ d₂ : SquareIntegrableLanglandsDatum.{uV, uF} F.canonicalTopologicalData n)
    (d₁' d₂' : SquareIntegrableLanglandsDatum.{uW, uF} F.canonicalTopologicalData t)
    (a : Fin d₁.shape.length ≃ Fin d₂.shape.length)
    (a' : Fin d₁'.shape.length ≃ Fin d₂'.shape.length)
    (ha : ∀ i, ∃ h : d₁.shape.size i = d₂.shape.size (a i),
      Nonempty ((h ▸ d₁.blocks i) ≅ d₂.blocks (a i)))
    (ha' : ∀ j, ∃ h : d₁'.shape.size j = d₂'.shape.size (a' j),
      Nonempty ((h ▸ d₁'.blocks j) ≅ d₂'.blocks (a' j)))
    {e₁ e₂ : ℂˣ × ℤ}
    (h₁ : IsSquareIntegrableDataEpsilonFactor F ψ ν d₁ d₁' e₁)
    (h₂ : IsSquareIntegrableDataEpsilonFactor F ψ ν d₂ d₂' e₂) : e₁ = e₂ := by
  obtain ⟨b₁, hb₁, rfl⟩ := h₁
  obtain ⟨b₂, hb₂, rfl⟩ := h₂
  have hb : b₁ = fun i j => b₂ (a i) (a' j) := by
    funext i j
    obtain ⟨hi, ⟨φ⟩⟩ := ha i
    obtain ⟨hj, ⟨φ'⟩⟩ := ha' j
    have h := (rankEpsilonFactor_congr_iso hi hj
      (d₁.blocks i) (d₁'.blocks j) (d₂.blocks (a i)) (d₂'.blocks (a' j))
      φ φ').mp (hb₁ i j)
    exact h.unique (hb₂ (a i) (a' j))
  rw [hb, epsilonFactorProduct_reindex]

end Invariance

section Classification

variable (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {r t : ℕ}
  (π : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uV} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier))
  (σ : letI := F.canonicalTopologicalData.topology
    SmoothRep.{0, uF, max uF uW} ℂ (Langlands.GeneralLinear (t + 1) F.Carrier))

/-- The published square-integrable classification implies datum independence
for epsilon products. Its two carrier universes are kept independent. -/
theorem langlandsPairEpsilonDataIndependence_of_classification
    (hπ : Classification.SquareIntegrableLanglandsClassification.{uF, uV}
      F F.canonicalTopologicalData)
    (hσ : Classification.SquareIntegrableLanglandsClassification.{uF, uW}
      F F.canonicalTopologicalData) :
    LanglandsPairEpsilonDataIndependence.{uF, max uF uV, max uF uW} F ψ ν π σ := by
  let := F.canonicalTopologicalData.topology
  intro d₁ d₂ d₁' d₂' hd₁ hd₂ hd₁' hd₂' e₁ e₂ he₁ he₂
  obtain ⟨a, ha⟩ := (hπ (r + 1) (Nat.succ_pos r) d₁ d₂ π π hd₁ hd₂).mp
    ⟨Iso.refl π⟩
  obtain ⟨a', ha'⟩ := (hσ (t + 1) (Nat.succ_pos t) d₁' d₂' σ σ hd₁' hd₂').mp
    ⟨Iso.refl σ⟩
  exact squareIntegrableDataEpsilonFactor_eq_of_matching
    d₁ d₂ d₁' d₂' a a' ha ha' he₁ he₂

/-- Construct the nongeneric epsilon pair from irreducibility, the published
classification/exhaustion propositions, and genuine block-factor existence.
Datum independence is derived inside the construction. -/
def langlandsPairEpsilonFactorOfClassification
    (hπ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible π.representation)
    (hσ : letI := F.canonicalTopologicalData.topology
      Representation.IsIrreducible σ.representation)
    (hexπ : Classification.SquareIntegrableLanglandsExhaustion.{uF, uV}
      F F.canonicalTopologicalData)
    (hexσ : Classification.SquareIntegrableLanglandsExhaustion.{uF, uW}
      F F.canonicalTopologicalData)
    (hclπ : Classification.SquareIntegrableLanglandsClassification.{uF, uV}
      F F.canonicalTopologicalData)
    (hclσ : Classification.SquareIntegrableLanglandsClassification.{uF, uW}
      F F.canonicalTopologicalData)
    (hb : LanglandsPairEpsilonBlockExistence.{uF, max uF uV, max uF uW} F ψ ν π σ) :
    {e : ℂˣ × ℤ //
      IsLanglandsPairEpsilonFactor.{uF, max uF uV, max uF uW} F ψ ν π σ e} := by
  have hdataπ : ∃ d : SquareIntegrableLanglandsDatum.{max uF uV, uF}
      F.canonicalTopologicalData (r + 1), d.IsLanglandsQuotient π := by
    obtain ⟨d, hd⟩ := hexπ (r + 1) (Nat.succ_pos r) π hπ
    exact ⟨d, hd.isLanglandsQuotient⟩
  have hdataσ : ∃ d : SquareIntegrableLanglandsDatum.{max uF uW, uF}
      F.canonicalTopologicalData (t + 1), d.IsLanglandsQuotient σ := by
    obtain ⟨d, hd⟩ := hexσ (t + 1) (Nat.succ_pos t) σ hσ
    exact ⟨d, hd.isLanglandsQuotient⟩
  exact langlandsPairEpsilonFactor F ψ ν π σ hdataπ hdataσ hb
    (langlandsPairEpsilonDataIndependence_of_classification F ψ ν π σ hclπ hclσ)

end Classification

end Langlands.RankinSelberg
