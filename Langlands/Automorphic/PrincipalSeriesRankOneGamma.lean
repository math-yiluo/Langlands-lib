import Langlands.Correspondence.RankOneAnalyticGaussEpsilon
import Langlands.Correspondence.RankOneAnalyticLFactor
import Langlands.Correspondence.SupercuspidalGammaFromFactorsProof
import Langlands.Representation.Unramified.PrincipalSeriesDuality
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Representation.Whittaker.FunctionalExistence

/-! # Rank-one gamma factors of pairs of quasi-characters -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Correspondence

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GodementJacquet Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
private local instance : MeasurableSpace F.Carrier := borel _
private local instance : BorelSpace F.Carrier := ⟨rfl⟩

/-- Tate's rational gamma function of a quasi-character `χ`:
`ε(0, χ, ψ, ν) X^(a(χ) + n(ψ)) L(χ)(X) / L(χ⁻¹)(q⁻¹ / X)`. -/
def tateRationalGamma (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (χ : QuasiCharacter F) : RatFunc ℂ :=
  rationalGammaExpression (LocalFactor.residueReflection F)
    (Padic.tateEpsilonCoefficient F ν χ ψ)
    (LocalFactor.PadicAbelian.epsilonExponent F.canonicalTopologicalData χ ψ)
    (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ)
    (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ⁻¹)

/-- The character representation `χ ∘ det` of `GL_1` is generic for every `ψ`. -/
theorem isGeneric_rankOneCharacter (ψ : NontrivialAdditiveCharacter F)
    (χ : QuasiCharacter F) :
    Whittaker.IsGeneric ψ 0 (rankOneCharacter χ.toMonoidHom) := by
  have : Representation.IsIrreducible (rankOneCharacter χ.toMonoidHom) :=
    Classification.isIrreducible_of_linearEquiv_complex _ (LinearEquiv.refl ℂ ℂ)
  exact Whittaker.isGeneric_rankOne ψ _ (rankOneCharacter_isOfWhittakerType p F ψ χ).1

/-- The JPSS gamma factor of two rank-one character representations is Tate's
rational gamma function of the product character, for a self-dual measure. -/
theorem isPadicPairGammaFactor_rankOneCharacters (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν) (χ η : QuasiCharacter F) :
    IsPadicPairGammaFactor F ψ ν (rankOneCharacter χ.toMonoidHom)
      (rankOneCharacter η.toMonoidHom) (tateRationalGamma F ψ ν (χ * η)) := by
  let νs : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨ν, hν⟩
  have he : IsPadicSymmetricEpsilonFactor F ψ ν (rankOneCharacter χ.toMonoidHom)
      (rankOneCharacter η.toMonoidHom)
      (Padic.tateEpsilonCoefficient F ν (χ * η) ψ,
        LocalFactor.PadicAbelian.epsilonExponent F.canonicalTopologicalData (χ * η) ψ) :=
    (isPadicSymmetricEpsilonFactor_of_le le_rfl).mpr
      (isPadicPairEpsilonFactor_rankOneCharacterEquiv_gauss F ψ ν hν
        (Representation.Equiv.refl _) (Representation.Equiv.refl _))
  have hP : IsPadicSymmetricLPolynomial F ψ ν (rankOneCharacter χ.toMonoidHom)
      (rankOneCharacter η.toMonoidHom)
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η)) :=
    (isPadicSymmetricLPolynomial_of_le le_rfl).mpr
      (isPadicPairLPolynomial_of_rankOneCharacterEquiv F ψ ν
        (Representation.Equiv.refl _) (Representation.Equiv.refl _))
  have hP' : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν
      (rankOneCharacter χ⁻¹.toMonoidHom) (rankOneCharacter η⁻¹.toMonoidHom)
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η)⁻¹) := by
    have hinv : (χ * η)⁻¹ = χ⁻¹ * η⁻¹ := mul_inv χ η
    rw [hinv]
    exact (isPadicSymmetricLPolynomial_of_le le_rfl).mpr
      (isPadicPairLPolynomial_of_rankOneCharacterEquiv F (ψ.scale (-1)) ν
        (Representation.Equiv.refl _) (Representation.Equiv.refl _))
  have h := isPadicSymmetricGammaFactor_of_smoothDual F ψ νs
    (rankOneCharacter χ.toMonoidHom) (rankOneCharacter η.toMonoidHom)
    (rankOneCharacter χ⁻¹.toMonoidHom) (rankOneCharacter η⁻¹.toMonoidHom)
    (isGeneric_rankOneCharacter F ψ χ) (isGeneric_rankOneCharacter F ψ η)
    (Unramified.scalarCharacterSmoothDualEquiv F χ)
    (Unramified.scalarCharacterSmoothDualEquiv F η) he hP hP'
  exact (isPadicSymmetricGammaFactor_of_le le_rfl).mp h

/-- The same formula for arbitrary representations equivalent to the two
character representations, in independent carrier universes. -/
theorem isPadicPairGammaFactor_of_rankOneCharacterEquiv (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν)
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V}
    {τ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) W}
    {χ η : QuasiCharacter F}
    (eπ : (rankOneCharacter χ.toMonoidHom).Equiv π)
    (eτ : (rankOneCharacter η.toMonoidHom).Equiv τ) :
    IsPadicPairGammaFactor F ψ ν π τ (tateRationalGamma F ψ ν (χ * η)) :=
  (IsPadicPairGammaFactor.congr_equiv eπ eτ).mp
    (isPadicPairGammaFactor_rankOneCharacters F ψ ν hν χ η)

end Langlands.Correspondence
