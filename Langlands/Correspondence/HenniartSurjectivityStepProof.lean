import Langlands.Correspondence.HenniartRankConductor
import Langlands.Correspondence.HenniartNumericalStatement

/-!
# The surjectivity step from Henniart's numerical theorem

Henniart (2000), §4.3, last sentence: in rank `n`, the stable images are
surjective onto the unitary supercuspidal classes with central character of
finite order, by Henniart (1988), Théorème 1.2. The extension of the stable
images of rank `n` by unramified twists is injective, commutes with unramified
twists and preserves conductors, so the numerical theorem makes it surjective,
and surjectivity of the stable images follows.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart (2000), §4.3 with Henniart (1988), Théorème 1.2: candidate existence,
normalized local reciprocity, local constants for every normalized family, the
surjectivity assertion of the numerical theorem, the conductor exponent of local
constants (Tate (3.4.5), Deligne (5.5.2)), the dependence of the exponent of
pair epsilon factors on the additive character (Bushnell–Henniart–Kutzko) and
the conductor exponent of generic representations (JPSS (5.1)) give the
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
  Conductor.ConductorExponentStatement.{uK, uV} →
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

end Langlands.Henniart.Extension
