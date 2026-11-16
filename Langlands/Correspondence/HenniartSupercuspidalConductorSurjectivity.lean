import Langlands.Correspondence.HenniartRankConductor
import Langlands.Correspondence.HenniartNumericalStatement
import Langlands.Correspondence.HenniartSupercuspidalConductorFiniteness

/-!
# Conductor preservation and surjectivity with the restricted conductor premise

The extension of stable images preserves conductors using the JPSS conductor premise
only for supercuspidal p-adic representations. Henniart's numerical surjectivity
premise therefore supplies the surjectivity step with this weaker conductor input.
-/

noncomputable section

namespace Langlands.Henniart.Extension.SupercuspidalConductor

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

universe uK uW uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartSupercuspidalRankConductorTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The conductor of a supercuspidal class with an epsilon factor `c q^(-ms)`
against the trivial character of `GL₁` is `m - (k+1) n(ψ)`. -/
theorem conductor_eq_of_pairEpsilon
    (hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0})
    (hJPSS : Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV})
    (ψ : NontrivialAdditiveCharacter K) (ν : LocalAdditiveHaarMeasure K)
    (hν : IsSelfDualMeasure K ψ ν) {k : ℕ}
    (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) {c : ℂˣ} {m : ℤ}
    (h : IsSupercuspidalPairEpsilonFactor K ψ ν (r := k) (n := 0) π
      (rankOneSupercuspidalClass.{uK, uV} K 1) (c, m)) :
    ∃ b : ℕ, (b : ℤ) = m - ((k + 1 : ℕ) : ℤ) * K.canonicalTopologicalData.additiveConductor ψ ∧
      Numerical.conductor K π = b := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨b, hb, hnew⟩ := exists_newvectorConductor_of_pairEpsilon K hBHK hJPSS ψ ν hν A h
  exact ⟨b, hb, firstFixedLevel_eq_of_isNewvectorConductor K hnew⟩

/-- The extension of the stable images of rank `k + 1` sends a Weil class of Artin
conductor `a` to a supercuspidal class of conductor `a`. -/
theorem rankExtension_conductor
    (hSC : ConductorExponent.SpectralConductorStatement.{uK, uW} K)
    (hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0})
    (hJPSS : Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e)
    {eC : ReciprocityFamily K} {ε : NonabelianSystem.Assignment.{uK, uW} K}
    (hε : NonabelianSystem.IsSystem K eC ε) {k : ℕ}
    (hS : StableExistsAt.{uK, uW, uV, uW} K k.succPNat)
    (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) {a : ℕ}
    (ha : Numerical.HasArtinConductor K σ a) :
    Numerical.conductor K (rankExtension K hS σ) = a := by
  obtain ⟨z, π₀, b₀, hdec, he₁⟩ := rankExtensionBasis_spec K hS σ
  have hrank₀ : π₀.val.1 = k.succPNat := by
    have := rankExtensionBasis_rank K hS σ
    rw [he₁] at this
    exact this
  obtain ⟨Q, _, _, q, hσq, ⟨W, A, Φ, hΦ⟩, hall⟩ := hdec.2
  have hΦx := hall W A Φ hΦ ⟨generator b₀, hΦ.1 hσq⟩ rfl
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists K K.canonicalTopologicalData
  obtain ⟨ν, hν⟩ := (hΦ.2.2.2 ψ).1
  have h1 : ∀ a : K.Carrierˣ, ‖((1 : QuasiCharacter K) a : ℂ)‖ = 1 := fun _ => by simp
  obtain ⟨x₁, π₁, hx₁, hπ₁, hΦx₁⟩ :=
    candidate_character_generator K hΦ.2 he 1 h1 (trivialWeilUnitary K e) rfl
  obtain ⟨c₀, hW, hG⟩ := candidate_pairEpsilon K hΦ.2 hε ψ ν hν ⟨generator b₀, hΦ.1 hσq⟩ x₁
    rfl hx₁ hΦx hΦx₁
  have hWA := LocalWeil.isArithmeticPairEpsilonFactor_of_generator K hW
  -- the Weil side
  obtain ⟨⟨m', σ₀⟩, hb₀u⟩ := b₀
  have hdec1 := hdec.1
  obtain ⟨rfl, hσheq⟩ := Sigma.mk.inj hdec1
  have hσ := eq_of_heq hσheq
  have hweil := weil_exponent_of_twist K hSC e eC ε hε ψ σ₀ σ z hσ.symm ha hWA
  -- the side of `GL_n`
  obtain ⟨⟨m₀, π₀'⟩, hπ₀u⟩ := π₀
  obtain rfl : m₀ = k.succPNat := hrank₀
  obtain ⟨⟨m₁, τ₁⟩, hτ₁⟩ := π₁
  obtain ⟨rfl, hτ⟩ := Sigma.mk.inj_iff.mp hπ₁
  cases hτ
  obtain ⟨c', hG'⟩ := isSupercuspidalPairEpsilonFactor_unramifiedTwist_left K
    RankinSelberg.unramifiedTwistEpsilon ψ ν hν (r := k) (n := 0) hG z
  obtain ⟨b, hb, hcond⟩ := conductor_eq_of_pairEpsilon K hBHK hJPSS ψ ν hν _ hG'
  have hφ : rankExtension K hS σ = supercuspidalTwist K (fieldUnramified K z) π₀' := by
    have h2 := (sigma_rankExtension K hS σ).trans he₁
    exact eq_of_heq (Sigma.mk.inj h2).2
  rw [hφ, hcond]
  have hbr : (b : ℝ) = a := by
    have hb' : (b : ℝ) = (c₀.2 : ℝ) - ((k + 1 : ℕ) : ℝ) *
        (K.canonicalTopologicalData.additiveConductor ψ : ℝ) := by
      exact_mod_cast hb
    rw [hb', hweil]
    push_cast
    ring
  have hba : b = a := by exact_mod_cast hbr
  rw [hba]

/-- Henniart (2000), §4.3 with Henniart (1988), Théorème 1.2: candidate existence,
normalized local reciprocity, local constants for every normalized family, the
surjectivity assertion of the numerical theorem, the conductor exponent of local
constants (Tate (3.4.5), Deligne (5.5.2)), the dependence of the exponent of
pair epsilon factors on the additive character (Bushnell–Henniart–Kutzko) and
the conductor exponent of supercuspidal p-adic representations (JPSS (5.1)) give the
surjectivity step. -/
def SurjectivityStepReductionStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  NumericalSurjectivityStatement.{uK, uW, uV} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
    ConductorExponent.SpectralConductorStatement.{uK, uW} K) →
  RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} →
  Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV} →
  SurjectivityStepStatement.{uK, uW, uV, uW}

/-- Proof of `SurjectivityStepReductionStatement`. -/
theorem surjectivityStepReduction : SurjectivityStepReductionStatement.{uK, uW, uV} := by
  intro hCE hrec hsys hnum hSC hBHK hJPSS p _ K n hS
  obtain ⟨eC, heC⟩ := hrec p K K.canonicalTopologicalData
  have he := baseGeometricReciprocityProof K eC heC
  obtain ⟨ε, hε⟩ := hsys p K eC heC
  have hUTI := unramifiedTwistIndependence_of_reciprocity hCE hrec
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, k.succPNat = n := ⟨n.natPred, PNat.succPNat_natPred n⟩
  have hinj : Numerical.IsNumericalInjection K (rankExtension K hS) :=
    ⟨rankExtension_injective K hS hCE he,
      fun σ a ha => rankExtension_conductor K (hSC p K) hBHK hJPSS he hε hS σ ha,
      fun z σ => rankExtension_twist K hS hUTI z σ⟩
  exact stableSurjectiveAt_of_surjective K hS hCE he (hnum p K k _ hinj)

end Langlands.Henniart.Extension.SupercuspidalConductor
