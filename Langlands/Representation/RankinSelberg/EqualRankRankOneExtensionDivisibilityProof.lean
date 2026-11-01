import Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonProof
import Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionDivisibilityStatement
import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence

/-!
# Equal-rank rank-one extension reverse L-divisibility: proof
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

section Shape

variable {p : ℕ} [Fact p.Prime]

/-- The ranks `(0, t)` of the ordered blocks `(χ, σ₁)`. -/
abbrev equalRankExtensionRanks (t : ℕ) : Fin 2 → ℕ := ![0, t]

theorem equalRankExtensionRankSum (t : ℕ) :
    ∑ i, (equalRankExtensionRanks t i + 1) = (1 + t) + 1 := by
  simp only [equalRankExtensionRanks, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  omega

/-- The blocks `(χ, σ₁)` indexed by the ranks `equalRankExtensionRanks t`. -/
def equalRankExtensionFamily {F : PadicField.{uF} p} {t : ℕ} {C W : Type uW}
    [AddCommGroup C] [Module ℂ C] [AddCommGroup W] [Module ℂ W]
    (χrep : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) C)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (i : Fin 2) : Representation ℂ
      (Langlands.GeneralLinear (equalRankExtensionRanks t i + 1) F.Carrier)
      (Shahidi.pairCarrier C W i) :=
  match i with
  | 0 => χrep
  | 1 => σ₁

/-- The full Whittaker type of the upper normalized induction of `(χ, σ₁)`, from
the published theorem `normalizedProductWhittakerType` for successor block
shapes. -/
theorem isOfWhittakerType_equalRankExtension
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    {t : ℕ} {C W : Type uW} [AddCommGroup C] [Module ℂ C] [AddCommGroup W] [Module ℂ W]
    (χrep : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) C)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (hχ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType 0 (standardCharacter ψ 0) χrep)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ₁) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
      (F.canonicalNormalizedProductInduced
        (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
        (Shahidi.pairFamily χrep σ₁)) := by
  let D := Σ s : {s : Fin 2 → ℕ // (∀ i, 0 < s i) ∧ ∑ i, s i = (1 + t) + 1},
    ∀ i, Representation ℂ (Langlands.GeneralLinear (s.val i) F.Carrier)
      (Shahidi.pairCarrier C W i)
  let d₀ : D := ⟨⟨fun i => equalRankExtensionRanks t i + 1,
    ⟨fun i => Nat.succ_pos _, equalRankExtensionRankSum t⟩⟩,
    equalRankExtensionFamily χrep σ₁⟩
  let d₁ : D := ⟨⟨![1, t + 1], ⟨by intro i; fin_cases i <;> exact Nat.succ_pos _,
    by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega⟩⟩,
    Shahidi.pairFamily χrep σ₁⟩
  have hd : d₀ = d₁ := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      fin_cases i <;> rfl
  let wt : D → Prop := fun d =>
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
      (F.canonicalNormalizedProductInduced ⟨2, d.1.val, d.1.property.1, d.1.property.2⟩ d.2)
  change wt d₁
  rw [← hd]
  apply normalizedProductWhittakerType.{uF, uW} p F ψ (1 + t) 2 (equalRankExtensionRanks t) (equalRankExtensionRankSum t)
    (equalRankExtensionFamily χrep σ₁)
  intro i
  fin_cases i
  · exact hχ
  · exact hσ

end Shape

/-- Reverse L-divisibility for the equal-rank rank-one extension, from the
published `symmetricLPolynomialExists`, `normalizedProductWhittakerType` and
`equalRankRankOneExtensionSpanComparison`. -/
theorem equalRankRankOneExtensionLDivisibility :
    EqualRankRankOneExtensionLDivisibilityStatement.{uF, uV, uW} := by
  intro p _ F ψ ν t V _ _ W _ _ π σ₁ χ hπ hσ χlift
  let := F.canonicalTopologicalData.topology
  have hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) χlift :=
    (rankOneCharacter_isOfWhittakerType p F ψ χ).of_equiv (conjULiftEquiv _)
  have hI := isOfWhittakerType_equalRankExtension F ψ χlift σ₁ hχ hσ
  obtain ⟨Pbase, hb⟩ := symmetricLPolynomialExists.{uF, uV, uW}
    p F ψ ν (t + 1) t V W π σ₁ hπ hσ
  obtain ⟨Pind, hi⟩ := symmetricLPolynomialExists.{uF, uV, max uF uW}
    p F ψ ν (t + 1) (1 + t) V _ π _ hπ hI
  refine ⟨Pbase, Pind, hb, hi, ?_⟩
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
  rw [isPadicSymmetricLPolynomial_of_le (by omega)] at hb
  rw [isPadicSymmetricLPolynomial_of_le (show 1 + t ≤ t + 1 by omega)] at hi
  obtain ⟨⟨_, μb, hμb⟩, hb'⟩ := hb
  obtain ⟨⟨_, μi, hμi⟩, hi'⟩ := hi
  have hrn : t + 1 = 1 + t := by omega
  have gb := (isPairLPolynomial_of_lt (by omega)).1 (hb' μb hμb) 0 0 rfl
  have gi := hi' μi hμi
  rw [IsPairLPolynomial, ite_eq_right (show ¬ (1 + t < t + 1) by omega), dite_eq_left hrn] at gi
  exact (laurentPolynomialDivisibility.2.2 _ _ _ _ gb gi).1
    (equalRankRankOneExtensionSpanComparison.{uF, uV, uW}
      p F ψ ν.val t π σ₁ χ hπ hσ μb μi hμb hμi hrn)

end Langlands.RankinSelberg
