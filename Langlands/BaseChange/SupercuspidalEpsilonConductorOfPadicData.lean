import Langlands.BaseChange.CuspidalSigmaLiftConductorLocalReduction
import Langlands.LocalField.SuppliedPadicNormalization
import Langlands.Global.Factors.GLPoleRegionTransport
import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof
import Langlands.Representation.Conductor.GenericEpsilonConductor
import Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeProof
import Langlands.Representation.RankinSelberg.PairEpsilonExponentProof
import Langlands.Representation.RankinSelberg.StableTwist.JPSSStability
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport

/-! # The epsilon exponent of a supercuspidal representation against the trivial character -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis RankinSelberg Whittaker
open scoped PadicField.CanonicalLocalField

universe u uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private theorem exists_canonical_standardEpsilonConductor
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hi : ρ.IsIrreducible) (hs : GeneralLinear.IsSupercuspidal ρ) :
    ∃ (a : ℕ) (e : ℂˣ × ℤ), IsStandardEpsilonConductor ψ ν.val ρ a e := by
  let T := F.canonicalTopologicalData
  let trivial := rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)
  let A := SmoothRep.of ρ hs.1.1
  have hgeneric (χ : UnitaryAdditiveCharacter F.Carrier) : IsGeneric χ r ρ :=
    SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal F χ r A hi hs
  obtain ⟨ψ₀, _, hψ₀, _⟩ := StableTwist.exists_conductorZero_scale F ψ
  let ν₀ := Correspondence.localSelfDualHaar F ψ₀
  have hν₀ := Correspondence.isSelfDual_localSelfDualHaar F ψ₀
  obtain ⟨ϖ, hϖ, hϖabs⟩ := HighlyRamified.exists_uniformizingElement_normalizedAbs F
  have hC := Conductor.supercuspidalPadicConductorExponent.{u, uV}
  obtain ⟨c₀, a, he₀, ha, _⟩ := @hC p _ F (show T2Space F.Carrier from inferInstance)
    (show TotallyDisconnectedSpace F.Carrier from inferInstance) (borel F.Carrier) ⟨rfl⟩
    (borel _) (@BorelSpace.mk _ _ (borel _) rfl) (borel _) (@BorelSpace.mk _ _ (borel _) rfl)
    (borel _) (@BorelSpace.mk _ _ (borel _) rfl) T.residueCardinality rfl
    (normalizedAbsoluteValue T) ϖ hϖ hϖabs
    (HighlyRamified.normalizedAbsoluteValue_eq_one F) ψ₀
    (HighlyRamified.hasIntegerConductor_of_additiveConductor_eq_zero F ψ₀ hψ₀)
    ν₀ hν₀ r V _ _ ρ (hgeneric ψ₀) hs
  have heps₀ : IsPadicPairEpsilonFactor F ψ₀ ν₀ ρ trivial (c₀, (a : ℤ)) := he₀
  obtain ⟨c, heps⟩ := Conductor.exists_isPadicPairEpsilonFactor_genericConductor F ψ ρ
    (hgeneric ψ) ν.val ν.property
  let e : ℂˣ × ℤ := (c, Conductor.genericConductor F ψ ρ (hgeneric ψ) +
    ((r + 1 : ℕ) : ℤ) * T.additiveConductor ψ)
  have htriv := UniformRankOneTwist.isGeneric_rankOneCharacter_one F ψ
  have hexp := pairEpsilonExponentReduction.{u, uV, 0} equalRankEpsilonCharacterChange
  obtain ⟨b, hb⟩ := hexp p F r 0 ρ trivial hi hs.1 htriv.1 htriv.2.1
  have hbase := hb ψ₀ ⟨ν₀, hν₀⟩ (c₀, (a : ℤ))
    ((isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le r)).mpr heps₀)
  have hb_eq : (a : ℤ) = b := by simpa only [hψ₀, mul_zero, add_zero] using hbase
  have he := hb ψ ν e ((isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le r)).mpr heps)
  refine ⟨a, e, ?_, ha, ?_⟩
  · exact heps
  · rw [← hb_eq] at he
    change e.2 = (a : ℤ) + ((r + 1 : ℕ) : ℤ) * T.toLocalFieldData.additiveConductor ψ
    rw [T.toLocalFieldData_additiveConductor]
    simpa only [Nat.zero_add, mul_one] using he

/-- The standard epsilon factor of a supercuspidal representation exists at
the supplied topology and valuation, with exponent the first fixed level plus
the rank times the additive conductor. -/
def SupercuspidalEpsilonConductorOfPadicDataStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar T ψ)
      (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V),
      ρ.IsIrreducible → GeneralLinear.IsSupercuspidal ρ →
      ∃ (a : ℕ) (e : ℂˣ × ℤ), IsStandardEpsilonConductor ψ ν.val ρ a e

theorem supercuspidalEpsilonConductorOfPadicData :
    SupercuspidalEpsilonConductorOfPadicDataStatement.{u, uV} := by
  intro p _ F T
  rw [T.eq_canonicalTopologicalData]
  exact exists_canonical_standardEpsilonConductor F

end Langlands.BaseChange
