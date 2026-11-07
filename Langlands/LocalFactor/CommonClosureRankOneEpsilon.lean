import Langlands.LocalFactor.CommonClosureGamma
import Langlands.LocalFactor.CommonClosureRankOneSpectral
import Langlands.VirtualRepresentation.ExactTensor

/-! # Conditional arithmetic epsilon values of character pairs -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.CommonClosure

attribute [simp] CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

@[simp]
theorem fieldCharacterEquiv_weilCharacter (e : ReciprocityFamily F) (E : Extension F)
    (χ : FieldCharacter F E) :
    CommonClosureSpectralAnalytic.fieldCharacterEquiv F e E (weilCharacter F e E χ) = χ :=
  (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e E).apply_symm_apply χ

end Langlands.LocalFactor.CommonClosure

namespace Langlands.LocalFactor.CommonClosureSpectral

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The exact spectral twist multiplies the actual continuous line character. -/
theorem virtualTwist_characterClass (E : Extension F)
    (χ : weilSubgroup F E →ₜ* ℂˣ) (s : ℂ) :
    virtualTwist F E s (ExactGrothendieckGroup.characterClass.{uF, max uF uV} χ) =
      ExactGrothendieckGroup.characterClass (character F E s * χ) :=
  ExactGrothendieckGroup.continuousTwist_characterClass _ _

/-- The supplied system evaluates a spectrally twisted line by its descended
field character and the actual abelian epsilon expression. -/
theorem conditionalDeligneValue_characterClass (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (χ : weilSubgroup F E →ₜ* ℂˣ) (s : ℂ) :
    (conditionalDeligneValue F e ε hε E ψ μ
      (ExactGrothendieckGroup.characterClass χ) s : ℂ) =
      (fieldData F E).abelianEpsilonExpression
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e E (character F E s * χ)) ψ μ := by
  rw [conditionalDeligneValue, virtualTwist_characterClass]
  simpa only [CommonClosure.characterClass, CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv] using
    hε.2.2.2.2 E (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e E (character F E s * χ)) ψ μ

end Langlands.LocalFactor.CommonClosureSpectral

namespace Langlands.LocalFactor.CommonClosureWeilDeligne

open CommonClosure CommonClosureSpectral

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A genuine lifted character line with zero monodromy and the actual norm. -/
def characterPair (E : Extension F) (χ : weilSubgroup F E →ₜ* ℂˣ) :
    Pair.{uF, uV} F E :=
  WeilDeligneRepresentation.zeroMonodromy (normCharacter F E).toMonoidHom
    (FiniteRepresentation.characterLine.{uF, max uF uV} χ.toMonoidHom)

theorem characterPair_isContinuous (E : Extension F) (χ : weilSubgroup F E →ₜ* ℂˣ) :
    (characterPair.{uF, uV} F E χ).toFiniteRepresentation.IsContinuous :=
  FiniteRepresentation.characterLine_isContinuous χ

@[simp]
theorem characterPair_monodromy (E : Extension F) (χ : weilSubgroup F E →ₜ* ℂˣ) :
    (characterPair.{uF, uV} F E χ).monodromy = 0 := rfl

@[simp]
theorem underlyingClass_characterPair (E : Extension F)
    (χ : weilSubgroup F E →ₜ* ℂˣ) :
    underlyingClass F E (characterPair.{uF, uV} F E χ)
      (characterPair_isContinuous F E χ) =
      VirtualRepresentation.ExactGrothendieckGroup.characterClass χ := rfl

/-- Both terms of the actual tensor monodromy vanish. -/
theorem characterPair_tensor_monodromy (E : Extension F)
    (χ η : weilSubgroup F E →ₜ* ℂˣ) :
    (WeilDeligneRepresentation.tensor
      (characterPair.{uF, uV} F E χ) (characterPair.{uF, uV} F E η)).monodromy = 0 := by
  change TensorProduct.map
      (0 : Module.End ℂ (characterPair.{uF, uV} F E χ))
      (1 : Module.End ℂ (characterPair.{uF, uV} F E η)) +
    TensorProduct.map
      (1 : Module.End ℂ (characterPair.{uF, uV} F E χ))
      (0 : Module.End ℂ (characterPair.{uF, uV} F E η)) = 0
  rw [TensorProduct.map_zero_left, TensorProduct.map_zero_right]
  exact add_zero 0

/-- Tensoring two actual character pairs gives the pair for their product. -/
def characterPairTensorEquiv (E : Extension F) (χ η : weilSubgroup F E →ₜ* ℂˣ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.tensor
        (characterPair.{uF, uV} F E χ) (characterPair.{uF, uV} F E η))
      (characterPair.{uF, uV} F E (χ * η)) where
  representationEquiv := by
    have f :=
      (FiniteRepresentation.tensorCharacterLineEquiv
        (FiniteRepresentation.characterLine.{uF, max uF uV} χ.toMonoidHom)
        η.toMonoidHom).trans
        (FiniteRepresentation.twistCharacterLineEquiv η.toMonoidHom χ.toMonoidHom)
    have hm : η.toMonoidHom * χ.toMonoidHom = (χ * η).toMonoidHom := by
      ext w
      change (η w : ℂ) * (χ w : ℂ) = (χ w : ℂ) * (η w : ℂ)
      exact mul_comm _ _
    rw [hm] at f
    exact f
  comm_monodromy := by
    rw [characterPair_tensor_monodromy, characterPair_monodromy,
      LinearMap.comp_zero, LinearMap.zero_comp]

/-- The full epsilon value of a line has trivial invariant-quotient correction. -/
theorem conditionalEpsilonValue_characterPair (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (χ : weilSubgroup F E →ₜ* ℂˣ) (Φ : GeometricFrobenius F E) (s : ℂ) :
    (conditionalEpsilonValue F e ε hε E ψ μ (characterPair F E χ)
      (characterPair_isContinuous F E χ) Φ s : ℂ) =
      (fieldData F E).abelianEpsilonExpression
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e E (character F E s * χ)) ψ μ := by
  rw [conditionalEpsilonValue_of_monodromy_zero F e ε hε E ψ μ _ _
    (characterPair_monodromy F E χ), underlyingClass_characterPair]
  exact conditionalDeligneValue_characterClass F e ε hε E ψ μ χ s

end Langlands.LocalFactor.CommonClosureWeilDeligne

namespace Langlands.LocalFactor.CommonClosureGamma

open CommonClosure CommonClosureSpectral CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Pair epsilon is the abelian expression of the descended spectral product
character, for every supplied actual Haar measure. -/
theorem conditionalPairEpsilonValue_characterPair (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (χ η : weilSubgroup F E →ₜ* ℂˣ) (Φ : GeometricFrobenius F E) (s : ℂ) :
    (conditionalPairEpsilonValue F e ε hε E ψ μ
      (characterPair F E χ) (characterPair F E η)
      (characterPair_isContinuous F E χ) (characterPair_isContinuous F E η) Φ s : ℂ) =
      (fieldData F E).abelianEpsilonExpression
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e E (character F E s * (χ * η))) ψ μ := by
  unfold conditionalPairEpsilonValue
  rw [conditionalEpsilonValue_eq_of_equiv F e ε hε E ψ μ _
    (characterPair_isContinuous F E (χ * η)) (characterPairTensorEquiv F E χ η) Φ s]
  exact conditionalEpsilonValue_characterPair F e ε hε E ψ μ (χ * η) Φ s

/-- The formula applies to arbitrary actual pairs through genuine pair
equivalences to the specified character lines. -/
theorem conditionalPairEpsilonValue_of_equiv_characterPair (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    {A B : Pair.{uF, uV} F E}
    (hA : A.toFiniteRepresentation.IsContinuous) (hB : B.toFiniteRepresentation.IsContinuous)
    (χ η : weilSubgroup F E →ₜ* ℂˣ)
    (f : WeilDeligneRepresentation.Equiv A (characterPair.{uF, uV} F E χ))
    (g : WeilDeligneRepresentation.Equiv B (characterPair.{uF, uV} F E η))
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    (conditionalPairEpsilonValue F e ε hε E ψ μ A B hA hB Φ s : ℂ) =
      (fieldData F E).abelianEpsilonExpression
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F e E (character F E s * (χ * η))) ψ μ := by
  rw [conditionalPairEpsilonValue_eq_of_equiv F e ε hε E ψ μ hA
    (characterPair_isContinuous F E χ) hB (characterPair_isContinuous F E η) f g Φ s]
  exact conditionalPairEpsilonValue_characterPair F e ε hε E ψ μ χ η Φ s

end Langlands.LocalFactor.CommonClosureGamma
