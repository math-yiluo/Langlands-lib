import Langlands.Correspondence.RankOneAnalyticEpsilonFactor
import Langlands.Representation.GodementJacquet.TateCharacterEpsilonFactor

/-! Actual rank-one automorphic epsilon certificates with concrete abelian Gauss data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Correspondence

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GodementJacquet

universe uF uP uA uB uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
private local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
private local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
private local instance : MeasurableSpace F.Carrier := borel _
private local instance : BorelSpace F.Carrier := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData

variable (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)
  (hν : IsSelfDualMeasure F ψ ν)

include hν

section Representatives

variable {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V}
  {τ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) W}
  {χ η : QuasiCharacter F}
  (eπ : (rankOneCharacter χ.toMonoidHom).Equiv π)
  (eτ : (rankOneCharacter η.toMonoidHom).Equiv τ)

include eπ eτ in
/-- Every genuine rank-one character realization has the full concrete epsilon certificate. -/
theorem isPadicPairEpsilonFactor_rankOneCharacterEquiv_gauss :
    IsPadicPairEpsilonFactor F ψ ν π τ
      (Padic.tateEpsilonCoefficient F ν (χ * η) ψ,
        LocalFactor.PadicAbelian.epsilonExponent T (χ * η) ψ) := by
  apply (isPadicPairEpsilonFactor_rankOneCharacterEquiv_iff F ψ ν eπ eτ _).mpr
  exact Padic.isPadicPairEpsilonFactor_tateCharacter F ψ (χ * η) ν hν

variable (hπ : Whittaker.IsGeneric ψ 0 π) (hτ : Whittaker.IsGeneric ψ 0 τ)

include eπ eτ in
/-- The existing selected coefficient and exponent are the actual Gauss data. -/
theorem genericPairEpsilonData_rankOneCharacterEquiv_gauss :
    genericPairEpsilonData F (Nat.le_refl 0) ψ ν hν π τ hπ hτ =
      (Padic.tateEpsilonCoefficient F ν (χ * η) ψ,
        LocalFactor.PadicAbelian.epsilonExponent T (χ * η) ψ) := by
  apply genericPairEpsilonData_eq
  exact isPadicPairEpsilonFactor_rankOneCharacterEquiv_gauss F ψ ν hν eπ eτ

include eπ eτ in
/-- The selected rational-function unit is the original rational abelian epsilon. -/
theorem coe_genericPairEpsilonFactor_rankOneCharacterEquiv_gauss :
    (genericPairEpsilonFactor F (Nat.le_refl 0) ψ ν hν π τ hπ hτ :
      RationalFunctions) =
      LocalFactor.PadicAbelian.rationalEpsilon T (χ * η) ψ ν := by
  rw [coe_genericPairEpsilonFactor,
    genericPairEpsilonData_rankOneCharacterEquiv_gauss F ψ ν hν eπ eτ hπ hτ,
    LocalFactor.PadicAbelian.rationalEpsilon_eq]
  rfl

include eπ eτ in
/-- Every selected spectral value is the existing callable abelian epsilon expression. -/
theorem coe_genericPairEpsilonValue_rankOneCharacterEquiv_gauss (s : ℂ) :
    (genericPairEpsilonValue F (Nat.le_refl 0) ψ ν hν π τ hπ hτ s : ℂ) =
      LocalFactor.PadicAbelian.epsilon T (χ * η) ψ ν.measure s := by
  rw [coe_genericPairEpsilonValue,
    genericPairEpsilonData_rankOneCharacterEquiv_gauss F ψ ν hν eπ eτ hπ hτ]
  exact Padic.epsilonMonomial_tateEpsilonCoefficient F ν (χ * η) ψ s

end Representatives

/-- The actual lifted supercuspidal classes satisfy the full concrete Gauss certificate. -/
theorem isSupercuspidalPairEpsilonFactor_rankOneSupercuspidalClass_gauss
    (χ η : QuasiCharacter F) :
    IsSupercuspidalPairEpsilonFactor F ψ ν
      (rankOneSupercuspidalClass.{uF, uA} F χ)
      (rankOneSupercuspidalClass.{uF, uB} F η)
      (Padic.tateEpsilonCoefficient F ν (χ * η) ψ,
        LocalFactor.PadicAbelian.epsilonExponent T (χ * η) ψ) := by
  apply (isSupercuspidalPairEpsilonFactor_rankOneSupercuspidalClass_iff
    F ψ ν χ η _).mpr
  exact Padic.isPadicPairEpsilonFactor_tateCharacter F ψ (χ * η) ν hν

/-- Any actual rank-one classes realizing the characters have the same concrete certificate. -/
theorem isSupercuspidalPairEpsilonFactor_of_rankOneCharacters_gauss
    {χ η : QuasiCharacter F}
    {π : SupercuspidalAutomorphicClass.{uF, uA} F 1}
    {τ : SupercuspidalAutomorphicClass.{uF, uB} F 1}
    (hπ : IsSupercuspidalRankOneCharacter F χ π)
    (hτ : IsSupercuspidalRankOneCharacter F η τ) :
    IsSupercuspidalPairEpsilonFactor F ψ ν π τ
      (Padic.tateEpsilonCoefficient F ν (χ * η) ψ,
        LocalFactor.PadicAbelian.epsilonExponent T (χ * η) ψ) := by
  apply (isSupercuspidalPairEpsilonFactor_of_isSupercuspidalRankOneCharacter_iff
    F ψ ν hπ hτ _).mpr
  exact Padic.isPadicPairEpsilonFactor_tateCharacter F ψ (χ * η) ν hν

/-- Actual images of the supplied rank-one reciprocity bijection have concrete
pair epsilon certificates for their actual field characters. -/
theorem rankOneReciprocityEquiv_pairEpsilonGauss
    (rec : ReciprocityCandidate F) (σ τ : IrreducibleWeilClass.{uF, uP} F 1) :
    ∃ χ η : QuasiCharacter F,
      IsRankOneWeilCharacter F (weilCharacter F rec χ) σ ∧
      IsRankOneWeilCharacter F (weilCharacter F rec η) τ ∧
      IsSupercuspidalPairEpsilonFactor F ψ ν
        (rankOneReciprocityEquiv.{uF, uP, uA} F rec σ)
        (rankOneReciprocityEquiv.{uF, uP, uB} F rec τ)
        (Padic.tateEpsilonCoefficient F ν (χ * η) ψ,
          LocalFactor.PadicAbelian.epsilonExponent T (χ * η) ψ) := by
  obtain ⟨χ, η, hχ, hη, hRed⟩ :=
    rankOneReciprocityEquiv_pairEpsilonReduction F ψ ν rec σ τ
  exact ⟨χ, η, hχ, hη, (hRed _).mpr
    (Padic.isPadicPairEpsilonFactor_tateCharacter F ψ (χ * η) ν hν)⟩

omit hν

/-- Concrete Gauss certificates on actual GL₁ classes, with independent carrier universes. -/
def RankOneAnalyticGaussEpsilonStatement : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F),
    IsSelfDualMeasure F ψ ν →
    ∀ χ η : QuasiCharacter F,
      IsSupercuspidalPairEpsilonFactor F ψ ν
        (rankOneSupercuspidalClass.{uF, uA} F χ)
        (rankOneSupercuspidalClass.{uF, uB} F η)
        (Padic.tateEpsilonCoefficient F ν (χ * η) ψ,
          LocalFactor.PadicAbelian.epsilonExponent T (χ * η) ψ)

theorem rankOneAnalyticGaussEpsilonStatement :
    RankOneAnalyticGaussEpsilonStatement.{uF, uA, uB} F := by
  intro ψ ν hν χ η
  exact isSupercuspidalPairEpsilonFactor_rankOneSupercuspidalClass_gauss F ψ ν hν χ η

end Langlands.Correspondence
