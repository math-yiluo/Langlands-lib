import Langlands.Representation.RankinSelberg.RankOneExtensionFactorTransport
import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof
import Langlands.Representation.RankinSelberg.RankOneExtensionDivisibilityStatement
import Langlands.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonProof

/-!
# Restricted rank-one extension reverse L-divisibility

The closed upper-induction form of JPSS Lemma 5.5, assembled from the
published strict span comparison, actual lower-to-upper factor transport,
full normalized Whittaker type and symmetric polynomial existence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

private abbrev extensionPredecessors (t : ℕ) : Fin 2 → ℕ := ![0, t]

private theorem extensionRankSum (t : ℕ) :
    ∑ i, (extensionPredecessors t i + 1) = (1 + t) + 1 := by
  simp only [extensionPredecessors, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

private def extensionFamily
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {t : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (χ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) (ULift.{uW} ℂ))
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (i : Fin 2) :
    Representation ℂ
      (Langlands.GeneralLinear (extensionPredecessors t i + 1) F.Carrier)
      (Shahidi.pairCarrier (ULift.{uW} ℂ) W i) :=
  match i with
  | 0 => χ
  | 1 => σ

/-- Conditional preservation specialized to the exact upper block family.
The dependent-data transport follows the published two-block assembly pattern;
no multiplicativity assertion is used. -/
theorem rankOneExtensionUpper_whittakerType_of_normalizedProduct
    (htype : NormalizedProductWhittakerTypeStatement.{uF, uW})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (t : ℕ) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (χ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) (ULift.{uW} ℂ))
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (hχ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType 0 (standardCharacter ψ 0) χ)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
      (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
        (Shahidi.pairFamily χ σ)) := by
  let := F.canonicalTopologicalData.topology
  have hblocks :
      ∀ i, IsOfWhittakerType (extensionPredecessors t i)
        (standardCharacter ψ (extensionPredecessors t i)) (extensionFamily χ σ i) := by
    intro i
    fin_cases i
    · exact hχ
    · exact hσ
  have hresult := htype p F ψ (1 + t) 2 (extensionPredecessors t)
    (extensionRankSum t) (extensionFamily χ σ) hblocks
  let D := Σ s : {s : Fin 2 → ℕ // (∀ i, 0 < s i) ∧ ∑ i, s i = (1 + t) + 1},
    ∀ i, Representation ℂ (Langlands.GeneralLinear (s.val i) F.Carrier)
      (Shahidi.pairCarrier (ULift.{uW} ℂ) W i)
  let d₀ : D := ⟨⟨fun i => extensionPredecessors t i + 1,
    ⟨fun i => Nat.succ_pos _, extensionRankSum t⟩⟩, extensionFamily χ σ⟩
  let d₁ : D := ⟨⟨![1, t + 1], ⟨by intro i; fin_cases i <;> exact Nat.succ_pos _,
    by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega⟩⟩,
    Shahidi.pairFamily χ σ⟩
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
  let property : D → Prop := fun d =>
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
      (F.canonicalNormalizedProductInduced
        ⟨2, d.1.val, d.1.property.1, d.1.property.2⟩ d.2)
  change property d₁
  have hresult' : property d₀ := hresult
  exact hd ▸ hresult'

/-- Construct the actual two certificates conditionally on the separately
owned full-type and common-existence statements at the needed universes. -/
theorem rankOneExtension_certificates_of_inputs
    (htype : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (hexistsBase : SymmetricLPolynomialExistenceStatement.{uF, uV, uW})
    (hexistsInd : SymmetricLPolynomialExistenceStatement.{uF, uV, max uF uW})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (hπ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) :
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
    ∃ Pbase Pind : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν.val π σ Pbase ∧
      IsPadicSymmetricLPolynomial F ψ ν.val π
        (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
          (Shahidi.pairFamily χlift σ)) Pind := by
  let := F.canonicalTopologicalData.topology
  let χlift : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier)
      (ULift.{uW} ℂ) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
      (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
  have hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) χlift :=
    rankOneExtensionCharacter_isOfWhittakerType F ψ χ
  have hind := rankOneExtensionUpper_whittakerType_of_normalizedProduct
    htype F ψ t χlift σ hχ hσ
  obtain ⟨Pbase, hbase⟩ := hexistsBase p F ψ ν r t V W π σ hπ hσ
  obtain ⟨Pind, hind⟩ := hexistsInd p F ψ ν r (1 + t) V _
    π (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
      (Shahidi.pairFamily χlift σ)) hπ hind
  exact ⟨Pbase, Pind, hbase, hind⟩

/-- The algebraic assembly, conditional on the actual certificates and the
strict base-to-lower-induced span comparison. -/
theorem rankOneExtensionLDivisibility_of_certificates_and_span
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) (ULift.{uW} ℂ))
    (hχ : letI := F.canonicalTopologicalData.topology; IsSmooth χ)
    (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ)
    (hrt : t + 3 ≤ r + 1)
    (Pbase Pind : ℂ[X])
    (hbase : IsPadicSymmetricLPolynomial F ψ ν.val π σ Pbase)
    (hind : IsPadicSymmetricLPolynomial F ψ ν.val π
      (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
        (Shahidi.pairFamily χ σ)) Pind) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
    (∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (1 + t))]
      (μbase : Measure (LeftUnipotentQuotient t F.Carrier))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F.Carrier)),
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F.Carrier)
        (generalLinearHaar F.Carrier (1 + t))
        (unipotentHaar F.Carrier (1 + t)) μind →
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := t)
        1 (r - t - 2) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μbase
        (rectangularMeasure ν.val 1 (t + 1)) π σ) ≤
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := 1 + t)
        0 (r - t - 2) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μind
        (rectangularMeasure ν.val 0 ((1 + t) + 1))
        π (rankOneExtensionLowerInduced F t χ σ))) →
      Pbase ∣ Pind := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
  let : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
  intro hspan
  have hlower : IsPadicSymmetricLPolynomial F ψ ν.val π
      (rankOneExtensionLowerInduced F t χ σ) Pind :=
    (rankOneExtensionSymmetricLPolynomial_iff F t χ σ hχ hσ ψ ν.val π Pind).2 hind
  have hbase' := (isPadicSymmetricLPolynomial_of_le (show t ≤ r by omega)).1 hbase
  have hlower' := (isPadicSymmetricLPolynomial_of_le (show 1 + t ≤ r by omega)).1 hlower
  obtain ⟨⟨hriBase, μbase, hμbase⟩, hgenBase⟩ := hbase'
  obtain ⟨⟨hriInd, μind, hμind⟩, hgenInd⟩ := hlower'
  let := hriBase
  let := hriInd
  have hB := (isPairLPolynomial_of_lt (show t < r by omega)).1
    (hgenBase μbase hμbase) 1 (r - t - 2) (by omega)
  have hI := (isPairLPolynomial_of_lt (show 1 + t < r by omega)).1
    (hgenInd μind hμind) 0 (r - t - 2) (by omega)
  exact (normalizedGeneratorSpanDivisibility _ _ Pbase Pind hB hI).1
    (hspan μbase μind hμbase hμind)

/-- Assemble the exact parent proposition from full type, common existence
at both carrier universes, and the strict span comparison. -/
theorem rankOneExtensionLDivisibility_of_inputs
    (htype : NormalizedProductWhittakerTypeStatement.{uF, uW})
    (hexistsBase : SymmetricLPolynomialExistenceStatement.{uF, uV, uW})
    (hexistsInd : SymmetricLPolynomialExistenceStatement.{uF, uV, max uF uW})
    (hspan : RankOneExtensionSpanComparisonStatement.{uF, uV, uW}) :
    RankOneExtensionLDivisibilityStatement.{uF, uV, uW} := by
  intro p hp F ψ ν r t V _ _ W _ _ π σ χ hrt hπ hσ
  let := F.canonicalTopologicalData.topology
  let χlift : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier)
      (ULift.{uW} ℂ) := rankOneExtensionCharacter F χ
  obtain ⟨Pbase, Pind, hbase, hind⟩ :=
    rankOneExtension_certificates_of_inputs htype hexistsBase hexistsInd
      F ψ ν r t π σ χ hπ hσ
  refine ⟨Pbase, Pind, hbase, hind, ?_⟩
  apply rankOneExtensionLDivisibility_of_certificates_and_span F ψ ν r t π σ χlift
    (rankOneExtensionCharacter_isSmooth F ψ χ) hσ.1.1 hrt Pbase Pind hbase hind
  exact hspan p F ψ ν r t π σ χ hrt hπ hσ

/-- JPSS Lemma 5.5 in its original strict rank range, for the actual ordered
upper normalized induction `(χlift, σ₁)`. Both certified polynomials and
the reverse divisibility are conclusions. -/
theorem rankOneExtensionLDivisibility :
    RankOneExtensionLDivisibilityStatement.{uF, uV, uW} :=
  rankOneExtensionLDivisibility_of_inputs
    normalizedProductWhittakerType.{uF, uW}
    symmetricLPolynomialExists.{uF, uV, uW}
    symmetricLPolynomialExists.{uF, uV, max uF uW}
    rankOneExtensionSpanComparison.{uF, uV, uW}

end Langlands.RankinSelberg
