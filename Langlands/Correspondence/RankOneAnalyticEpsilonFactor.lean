import Langlands.Representation.RankinSelberg.RankOneEpsilonTwist
import Langlands.Representation.RankinSelberg.PadicSymmetricEpsilonFactor
import Langlands.Correspondence.RankOneReciprocityBijection
import Langlands.Correspondence.SupercuspidalFactorCompatibility

/-! Full rank-one epsilon product reduction on actual representations and classes. -/

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

/-- Genuine equivalences preserve the entire epsilon product reduction. -/
theorem isPadicPairEpsilonFactor_rankOneCharacterEquiv_iff
    (eπ : (rankOneCharacter χ.toMonoidHom).Equiv π)
    (eτ : (rankOneCharacter η.toMonoidHom).Equiv τ) (e : ℂˣ × ℤ) :
    IsPadicPairEpsilonFactor F ψ ν π τ e ↔
      IsPadicPairEpsilonFactor F ψ ν
        (rankOneCharacter (χ * η).toMonoidHom) (rankOneCharacter 1) e := by
  exact (IsPadicPairEpsilonFactor.congr_equiv eπ eτ).symm.trans
    (isPadicPairEpsilonFactor_rankOneCharacters_mul F ψ ν
      χ.toMonoidHom η.toMonoidHom e)

variable (hν : IsSelfDualMeasure F ψ ν)
  (eπ : (rankOneCharacter χ.toMonoidHom).Equiv π)
  (eτ : (rankOneCharacter η.toMonoidHom).Equiv τ)
  (hπ : Whittaker.IsGeneric ψ 0 π) (hτ : Whittaker.IsGeneric ψ 0 τ)
  (hprod : Whittaker.IsGeneric ψ 0 (rankOneCharacter (χ * η).toMonoidHom))
  (h1 : Whittaker.IsGeneric ψ 0
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)))

include eπ eτ in
/-- Uniqueness identifies the selected coefficient and exponent with those
of the product character paired with the trivial character. -/
theorem genericPairEpsilonData_rankOneCharacterEquiv :
    genericPairEpsilonData F (Nat.le_refl 0) ψ ν hν π τ hπ hτ =
      genericPairEpsilonData F (Nat.le_refl 0) ψ ν hν
        (rankOneCharacter (χ * η).toMonoidHom) (rankOneCharacter 1) hprod h1 := by
  apply genericPairEpsilonData_eq
  exact (isPadicPairEpsilonFactor_rankOneCharacterEquiv_iff F ψ ν eπ eτ _).mpr
    (genericPairEpsilonData_isPadic F (Nat.le_refl 0) ψ ν hν _ _ hprod h1)

include eπ eτ in
/-- The selected epsilon rational-function units coincide. -/
theorem genericPairEpsilonFactor_rankOneCharacterEquiv :
    genericPairEpsilonFactor F (Nat.le_refl 0) ψ ν hν π τ hπ hτ =
      genericPairEpsilonFactor F (Nat.le_refl 0) ψ ν hν
        (rankOneCharacter (χ * η).toMonoidHom) (rankOneCharacter 1) hprod h1 := by
  unfold genericPairEpsilonFactor
  rw [genericPairEpsilonData_rankOneCharacterEquiv F ψ ν hν eπ eτ hπ hτ hprod h1]

include eπ eτ in
/-- The selected epsilon values coincide at every complex spectral parameter. -/
theorem genericPairEpsilonValue_rankOneCharacterEquiv (s : ℂ) :
    genericPairEpsilonValue F (Nat.le_refl 0) ψ ν hν π τ hπ hτ s =
      genericPairEpsilonValue F (Nat.le_refl 0) ψ ν hν
        (rankOneCharacter (χ * η).toMonoidHom) (rankOneCharacter 1) hprod h1 s := by
  apply Units.ext
  rw [coe_genericPairEpsilonValue, coe_genericPairEpsilonValue,
    genericPairEpsilonData_rankOneCharacterEquiv F ψ ν hν eπ eτ hπ hτ hprod h1]

end Representatives

/-- The existing epsilon relation on actual lifted GL₁ classes is precisely
the full product-character scalar relation. -/
theorem isSupercuspidalPairEpsilonFactor_rankOneSupercuspidalClass_iff
    (χ η : QuasiCharacter F) (e : ℂˣ × ℤ) :
    IsSupercuspidalPairEpsilonFactor F ψ ν
        (rankOneSupercuspidalClass.{uF, uA} F χ)
        (rankOneSupercuspidalClass.{uF, uB} F η) e ↔
      IsPadicPairEpsilonFactor F ψ ν
        (rankOneCharacter (χ * η).toMonoidHom) (rankOneCharacter 1) e := by
  change IsPadicSymmetricEpsilonFactor F ψ ν
    (rankOneSupercuspidalObject.{uF, uA} F χ).obj.representation
    (rankOneSupercuspidalObject.{uF, uB} F η).obj.representation e ↔ _
  rw [isPadicSymmetricEpsilonFactor_of_le (Nat.le_refl 0)]
  exact isPadicPairEpsilonFactor_rankOneCharacterEquiv_iff F ψ ν
    (FiniteRepresentation.characterLineEquiv.{uF, uA}
      (determinantQuasiCharacter F 1 χ)).symm
    (FiniteRepresentation.characterLineEquiv.{uF, uB}
      (determinantQuasiCharacter F 1 η)).symm e

/-- The same equivalence holds for any actual classes realizing the characters. -/
theorem isSupercuspidalPairEpsilonFactor_of_isSupercuspidalRankOneCharacter_iff
    {χ η : QuasiCharacter F}
    {π : SupercuspidalAutomorphicClass.{uF, uA} F 1}
    {τ : SupercuspidalAutomorphicClass.{uF, uB} F 1}
    (hπ : IsSupercuspidalRankOneCharacter F χ π)
    (hτ : IsSupercuspidalRankOneCharacter F η τ) (e : ℂˣ × ℤ) :
    IsSupercuspidalPairEpsilonFactor F ψ ν π τ e ↔
      IsPadicPairEpsilonFactor F ψ ν
        (rankOneCharacter (χ * η).toMonoidHom) (rankOneCharacter 1) e := by
  rw [IsSupercuspidalRankOneCharacter.class_unique F hπ
    (rankOneSupercuspidalClass_spec F χ),
    IsSupercuspidalRankOneCharacter.class_unique F hτ
      (rankOneSupercuspidalClass_spec F η)]
  exact isSupercuspidalPairEpsilonFactor_rankOneSupercuspidalClass_iff F ψ ν χ η e

/-- The actual reciprocity bijection reduces pair epsilon compatibility to
the product-character scalar relation. Reciprocity is supplied. -/
theorem rankOneReciprocityEquiv_pairEpsilonReduction
    (rec : ReciprocityCandidate F) (σ τ : IrreducibleWeilClass.{uF, uP} F 1) :
    ∃ χ η : QuasiCharacter F,
      IsRankOneWeilCharacter F (weilCharacter F rec χ) σ ∧
      IsRankOneWeilCharacter F (weilCharacter F rec η) τ ∧
      ∀ e : ℂˣ × ℤ,
        IsSupercuspidalPairEpsilonFactor F ψ ν
            (rankOneReciprocityEquiv.{uF, uP, uA} F rec σ)
            (rankOneReciprocityEquiv.{uF, uP, uB} F rec τ) e ↔
          IsPadicPairEpsilonFactor F ψ ν
            (rankOneCharacter (χ * η).toMonoidHom) (rankOneCharacter 1) e := by
  obtain ⟨χ, hσ⟩ := exists_rankOneWeilFieldCharacter F rec σ
  obtain ⟨η, hτ⟩ := exists_rankOneWeilFieldCharacter F rec τ
  refine ⟨χ, η, hσ, hτ, ?_⟩
  intro e
  exact isSupercuspidalPairEpsilonFactor_of_isSupercuspidalRankOneCharacter_iff
    F ψ ν (rankOneReciprocityEquiv_spec F rec χ σ hσ)
      (rankOneReciprocityEquiv_spec F rec η τ hτ) e

/-- Complete product reduction for actual rank-one class epsilon certificates,
with every additive character and additive Haar measure. -/
def RankOneEpsilonProductReductionStatement : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
    (χ η : QuasiCharacter F) (e : ℂˣ × ℤ),
    IsSupercuspidalPairEpsilonFactor F ψ ν
        (rankOneSupercuspidalClass.{uF, uA} F χ)
        (rankOneSupercuspidalClass.{uF, uB} F η) e ↔
      IsPadicPairEpsilonFactor F ψ ν
        (rankOneCharacter (χ * η).toMonoidHom) (rankOneCharacter 1) e

theorem rankOneEpsilonProductReductionStatement :
    RankOneEpsilonProductReductionStatement.{uF, uA, uB} F := by
  intro ψ ν χ η e
  exact isSupercuspidalPairEpsilonFactor_rankOneSupercuspidalClass_iff F ψ ν χ η e

end Langlands.Correspondence
