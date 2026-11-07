import Langlands.Representation.GodementJacquet.TateCharacterLFactor
import Langlands.Correspondence.RankOneArithmeticLFactor
import Langlands.Correspondence.SupercuspidalFactorCompatibility

/-! # Pair L-factors of the actual rank-one correspondence -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Correspondence

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GeneralLinear
  QuotientIntegration Polynomial

universe uF uP uA uB uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
private local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
private local instance : MeasurableSpace F.Carrier := borel _
private local instance : BorelSpace F.Carrier := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
private local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)

section Representatives

variable {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V}
  {τ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) W}
  {χ η : QuasiCharacter F}

/-- The exact polynomial is preserved by genuine equivalences of both members,
even when their carriers have different universes. -/
theorem isPadicPairLPolynomial_of_rankOneCharacterEquiv
    (eπ : (rankOneCharacter χ.toMonoidHom).Equiv π)
    (eτ : (rankOneCharacter η.toMonoidHom).Equiv τ) :
    IsPadicPairLPolynomial F ψ ν π τ
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η)) :=
  (IsPadicPairLPolynomial.congr_equiv eπ eτ).mp
    (GodementJacquet.Padic.rankOneCharacters_isPadicPairLPolynomial F χ ψ η ν)

/-- The selected p-adic JPSS polynomial has the explicit product-character value. -/
theorem padicPairLPolynomial_of_rankOneCharacterEquiv
    (eπ : (rankOneCharacter χ.toMonoidHom).Equiv π)
    (eτ : (rankOneCharacter η.toMonoidHom).Equiv τ)
    (hπ : IsOfWhittakerType 0 (standardCharacter ψ 0) π)
    (hτ : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0) τ) :
    padicPairLPolynomial F F.canonicalTopologicalData (Nat.le_refl 0)
      ψ ν π τ hπ hτ =
      LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η) := by
  exact padicPairLPolynomial_eq F F.canonicalTopologicalData (Nat.le_refl 0)
    ψ ν π τ hπ hτ (unipotentQuotientHaar F.Carrier 0)
    (unipotentQuotientHaar_isCompatible F.Carrier 0)
    ((isPadicPairLPolynomial_of_rankOneCharacterEquiv F ψ ν eπ eτ).2
      (unipotentQuotientHaar F.Carrier 0)
      (unipotentQuotientHaar_isCompatible F.Carrier 0))

/-- The selected p-adic JPSS rational-function unit is the abelian L-factor. -/
theorem padicPairLFactor_of_rankOneCharacterEquiv
    (eπ : (rankOneCharacter χ.toMonoidHom).Equiv π)
    (eτ : (rankOneCharacter η.toMonoidHom).Equiv τ)
    (hπ : IsOfWhittakerType 0 (standardCharacter ψ 0) π)
    (hτ : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0) τ) :
    (padicPairLFactor F F.canonicalTopologicalData (Nat.le_refl 0)
      ψ ν π τ hπ hτ : RationalFunctions) =
      LocalFactor.PadicAbelian.rationalLFactor F.canonicalTopologicalData (χ * η) := by
  rw [coe_padicPairLFactor,
    padicPairLPolynomial_of_rankOneCharacterEquiv F ψ ν eπ eτ hπ hτ]
  rfl

/-- The existing selected generic L-factor has the same explicit value. -/
theorem genericPairLFactor_of_rankOneCharacterEquiv
    (eπ : (rankOneCharacter χ.toMonoidHom).Equiv π)
    (eτ : (rankOneCharacter η.toMonoidHom).Equiv τ)
    (hπ : Whittaker.IsGeneric ψ 0 π) (hτ : Whittaker.IsGeneric ψ 0 τ) :
    (genericPairLFactor F (Nat.le_refl 0) ψ ν π τ hπ hτ : RationalFunctions) =
      LocalFactor.PadicAbelian.rationalLFactor F.canonicalTopologicalData (χ * η) :=
  genericPairLFactor_eq F (Nat.le_refl 0) ψ ν π τ hπ hτ
    (isPadicPairLPolynomial_of_rankOneCharacterEquiv F ψ ν eπ eτ)

end Representatives

/-- The existing quotient-level JPSS relation holds for the actual lifted
rank-one supercuspidal classes, in independent carrier universes. -/
theorem isSupercuspidalPairLPolynomial_rankOneSupercuspidalClass
    (χ η : QuasiCharacter F) :
    IsSupercuspidalPairLPolynomial F ψ ν
      (rankOneSupercuspidalClass.{uF, uA} F χ)
      (rankOneSupercuspidalClass.{uF, uB} F η)
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η)) := by
  change IsPadicSymmetricLPolynomial F ψ ν
    (rankOneSupercuspidalObject.{uF, uA} F χ).obj.representation
    (rankOneSupercuspidalObject.{uF, uB} F η).obj.representation _
  apply (isPadicSymmetricLPolynomial_of_le (Nat.le_refl 0)).mpr
  exact isPadicPairLPolynomial_of_rankOneCharacterEquiv F ψ ν
    (FiniteRepresentation.characterLineEquiv.{uF, uA}
      (determinantQuasiCharacter F 1 χ)).symm
    (FiniteRepresentation.characterLineEquiv.{uF, uB}
      (determinantQuasiCharacter F 1 η)).symm

/-- Any actual rank-one classes realizing the specified characters have the
same certified polynomial. -/
theorem isSupercuspidalPairLPolynomial_of_isSupercuspidalRankOneCharacter
    {χ η : QuasiCharacter F}
    {π : SupercuspidalAutomorphicClass.{uF, uA} F 1}
    {τ : SupercuspidalAutomorphicClass.{uF, uB} F 1}
    (hπ : IsSupercuspidalRankOneCharacter F χ π)
    (hτ : IsSupercuspidalRankOneCharacter F η τ) :
    IsSupercuspidalPairLPolynomial F ψ ν π τ
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η)) := by
  rw [IsSupercuspidalRankOneCharacter.class_unique F hπ
    (rankOneSupercuspidalClass_spec F χ),
    IsSupercuspidalRankOneCharacter.class_unique F hτ
      (rankOneSupercuspidalClass_spec F η)]
  exact isSupercuspidalPairLPolynomial_rankOneSupercuspidalClass F ψ ν χ η

/-- The actual rank-one bijection preserves pair L-factors along supplied
geometric reciprocity, for every additive Haar measure. -/
theorem rankOneReciprocityEquiv_pairLCompatibility {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) :
    ∃ P : ℂ[X],
      IsSupercuspidalPairLPolynomial F ψ ν
        (rankOneReciprocityEquiv.{uF, uP, uA} F e σ)
        (rankOneReciprocityEquiv.{uF, uP, uB} F e τ) P ∧
      arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) =
        (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ := by
  obtain ⟨χ, hσ⟩ := exists_rankOneWeilFieldCharacter F e σ
  obtain ⟨η, hτ⟩ := exists_rankOneWeilFieldCharacter F e τ
  refine ⟨LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (χ * η), ?_, ?_⟩
  · exact isSupercuspidalPairLPolynomial_of_isSupercuspidalRankOneCharacter F ψ ν
      (rankOneReciprocityEquiv_spec F e χ σ hσ)
      (rankOneReciprocityEquiv_spec F e η τ hτ)
  · exact arithmeticPairLFactor_of_isRankOneWeilCharacter F he hσ hτ

/-- The separate pair-L assertion for the actual rank-one correspondence.
No self-dual normalization of the supplied additive Haar measure is required. -/
def RankOnePairLCompatibilityStatement (e : ReciprocityCandidate F) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1),
    ∃ P : ℂ[X],
      IsSupercuspidalPairLPolynomial F ψ ν
        (rankOneReciprocityEquiv.{uF, uP, uA} F e σ)
        (rankOneReciprocityEquiv.{uF, uP, uB} F e τ) P ∧
      arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) =
        (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹

theorem rankOnePairLCompatibilityStatement {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) :
    RankOnePairLCompatibilityStatement.{uF, uP, uA, uB} F e := by
  intro ψ ν σ τ
  exact rankOneReciprocityEquiv_pairLCompatibility F ψ ν he σ τ

/-- Any two families satisfying the existing rank-one compatibility condition
have the required separate pair-L comparison in rank one. -/
theorem SupercuspidalRankOneCompatibility.pairLCompatibility
    {e : ReciprocityCandidate F} (he : IsGeometricReciprocity F e)
    {c : SupercuspidalMap.{uF, uP, uA} F}
    {d : SupercuspidalMap.{uF, uP, uB} F}
    (hc : SupercuspidalRankOneCompatibility F e c)
    (hd : SupercuspidalRankOneCompatibility F e d)
    (σ τ : IrreducibleWeilClass.{uF, uP} F 1) :
    ∃ P : ℂ[X],
      IsSupercuspidalPairLPolynomial F ψ ν (c 1 σ) (d 1 τ) P ∧
      arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) =
        (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ := by
  rw [(supercuspidalRankOneCompatibility_iff_eq F e c).mp hc,
    (supercuspidalRankOneCompatibility_iff_eq F e d).mp hd]
  exact rankOneReciprocityEquiv_pairLCompatibility F ψ ν he σ τ

end Langlands.Correspondence
