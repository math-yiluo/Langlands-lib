import Langlands.Correspondence.RankOneEpsilonCharacterTransport
import Langlands.LocalField.Normalization.SpectralCharacter

/-! # Normalized spectral characters in rank-one arithmetic epsilon values -/

noncomputable section

universe uF uP uV

namespace Langlands.LocalFactor.CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Normalized reciprocity pulls the actual normalized absolute-value power
back to the common-closure spectral character at the same complex parameter. -/
theorem weilCharacter_normalizedAbsPowerCharacter
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (E : Extension F) (s : ℂ) :
    weilCharacter F e E ((fieldData F E).normalizedAbsPowerCharacter s) =
      CommonClosureSpectral.character F E s := by
  apply ContinuousMonoidHom.ext
  intro w
  apply Units.ext
  change ((fieldData F E).normalizedAbsPowerCharacter s
    (reciprocityUnits F e E w) : ℂ) = _
  rw [PadicField.TopologicalData.normalizedAbsPowerCharacter_apply,
    CommonClosureSpectral.character_apply]
  have h := he.2 E (LocalClassField.abelianizationProjection (weilSubgroup F E) w)
  change (fieldData F E).normalizedAbs
      ((reciprocityUnits F e E w : E.fieldˣ) : E.field) =
    (F.canonicalTopologicalData.residueCardinality : ℝ) ^
      (-(CommonClosureSpectral.baseDegree F E w).toAdd) at h
  rw [h, Real.log_zpow, ← Complex.exp_int_mul]
  congr 1
  change s * Complex.ofReal (((-(Weil.Local.localDegree F w.val).toAdd : ℤ) : ℝ) *
      Real.log (F.canonicalTopologicalData.residueCardinality : ℝ)) =
    ((Weil.Local.localDegree F w.val).toAdd : ℂ) *
      (-s * (Real.log (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ))
  push_cast
  ring

/-- Descent through a supplied normalized family identifies the spectral
character with the actual normalized absolute-value power. -/
theorem fieldCharacterEquiv_spectralCharacter
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e)
    (E : Extension F) (s : ℂ) :
    CommonClosureSpectralAnalytic.fieldCharacterEquiv F e E
        (CommonClosureSpectral.character F E s) =
      (fieldData F E).normalizedAbsPowerCharacter s := by
  rw [← weilCharacter_normalizedAbsPowerCharacter F e he E s,
    fieldCharacterEquiv_weilCharacter]

end Langlands.LocalFactor.CommonClosure

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance normalizedEpsilonBaseTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance normalizedEpsilonBottomTopology : TopologicalSpace (baseExtension F).field :=
  (fieldData F (baseExtension F)).topology

/-- The canonical bottom-field transport preserves normalized absolute-value powers. -/
theorem baseFieldCharacterEquiv_normalizedAbsPowerCharacter (s : ℂ) :
    baseFieldCharacterEquiv F (F.canonicalTopologicalData.normalizedAbsPowerCharacter s) =
      (fieldData F (baseExtension F)).normalizedAbsPowerCharacter s := by
  apply ContinuousMonoidHom.ext
  intro a
  apply Units.ext
  rw [baseFieldCharacterEquiv_apply,
    PadicField.TopologicalData.normalizedAbsPowerCharacter_apply,
    PadicField.TopologicalData.normalizedAbsPowerCharacter_apply]
  have h := PadicField.CanonicalTransport.normalizedAbs_map
    ((baseExtension F).asPadicField (p := p)) F (baseFieldPadicEquiv F)
    (a : (baseExtension F).field)
  change F.canonicalTopologicalData.normalizedAbs
      (baseFieldUnitsEquiv F a : F.Carrier) =
    (fieldData F (baseExtension F)).normalizedAbs (a : (baseExtension F).field) at h
  rw [h]

/-- Under normalized compatible reciprocity, spectral descent is the transport
of the original product times the actual base absolute-value power. -/
theorem fieldCharacterEquiv_normalized_rankOneSpectralProduct
    {e : ReciprocityCandidate F} {eC : ReciprocityFamily F}
    (h : IsBaseReciprocity F e eC) (he : NormalizedReciprocity F eC)
    (χ η : QuasiCharacter F) (s : ℂ) :
    CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC (baseExtension F)
      (CommonClosureSpectral.character F (baseExtension F) s *
        (baseRestrictedWeilCharacter F (RankOne.weilCharacter F e χ) *
          baseRestrictedWeilCharacter F (RankOne.weilCharacter F e η))) =
      baseFieldCharacterEquiv F
        (F.canonicalTopologicalData.normalizedAbsPowerCharacter s * (χ * η)) := by
  rw [fieldCharacterEquiv_rankOneSpectralProduct F h χ η s,
    fieldCharacterEquiv_spectralCharacter F eC he,
    baseFieldCharacterEquiv_mul F
      (F.canonicalTopologicalData.normalizedAbsPowerCharacter s) (χ * η),
    baseFieldCharacterEquiv_normalizedAbsPowerCharacter]

/-- The full rank-one pair epsilon value is the actual abelian expression
of the transported product with its normalized absolute-value power. -/
theorem conditionalPairEpsilonValue_of_normalized_rankOneBaseRestriction
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (χ η : QuasiCharacter F)
    (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    {A B : Pair.{uF, uV} F (baseExtension F)}
    (hA : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ)) A)
    (hB : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) B)
    (hAc : A.toFiniteRepresentation.IsContinuous) (hBc : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ) :
    (CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
      A B hAc hBc Φ s : ℂ) =
      (fieldData F (baseExtension F)).abelianEpsilonExpression
        (baseFieldCharacterEquiv F
          (F.canonicalTopologicalData.normalizedAbsPowerCharacter s * (χ * η))) ψ' μ := by
  rw [conditionalPairEpsilonValue_of_rankOneBaseRestriction
    F e eC ε hε χ η ψ' μ hA hB hAc hBc Φ s,
    fieldCharacterEquiv_normalized_rankOneSpectralProduct F h hε.1 χ η s]

/-- The normalized expression is equivalent to the full arithmetic certificate,
with every harmonic existence and universal clause retained. -/
theorem isArithmeticPairEpsilonFactor_normalized_rankOneWeilCharacterClass_iff
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (χ η : QuasiCharacter F) (c : ℂˣ) (m : ℤ) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ))
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) c m ↔
      (∃ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F)),
        IsBaseCharacter F ψ ψ' ∧ CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ) ∧
      Nonempty (GeometricFrobenius F (baseExtension F)) ∧
      ∀ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F)),
        IsBaseCharacter F ψ ψ' →
        CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ →
        ∀ s : ℂ,
          (fieldData F (baseExtension F)).abelianEpsilonExpression
            (baseFieldCharacterEquiv F
              (F.canonicalTopologicalData.normalizedAbsPowerCharacter s * (χ * η))) ψ' μ =
            RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality c m s := by
  rw [isArithmeticPairEpsilonFactor_rankOneWeilCharacterClass_iff
    F e eC ε hε ψ χ η c m]
  simp_rw [fieldCharacterEquiv_normalized_rankOneSpectralProduct F h hε.1 χ η]

end Langlands.Correspondence
