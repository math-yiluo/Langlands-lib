import Langlands.Correspondence.HenniartCandidateBaseChangeCompatibility
import Langlands.Correspondence.HenniartSupercuspidalConductorReductionProof
import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof
import Langlands.Correspondence.HenniartRankOneStageProof
import Langlands.Correspondence.HenniartChoiceIndependenceStepProof
import Langlands.Correspondence.HenniartSurjectivityTransfer

noncomputable section

namespace Langlands.Henniart

universe uK uW uV

open Langlands.Correspondence StableMap Numerical LocalFactor LocalFactor.CommonClosure

theorem candidateCompatibleNumericalInjectionsReduction :
    CandidateCompatibleNumericalInjectionsReductionStatement.{uK, uW, uV} := by
  intro hCE hBC p _ S N hsurj
  have hrec := LocalClassField.commonClosureReciprocityExistence.{uK}
  have hsys : ∀ (q : ℕ) [Fact q.Prime] (K : PadicField.{uK} q) (eC : ReciprocityFamily K),
      NonabelianSystem.Exists.{uK, uW} K eC :=
    fun _ _ K eC => NonabelianSystem.exists_system K eC
  have hSC : ∀ (q : ℕ) [Fact q.Prime] (K : PadicField.{uK} q),
      ConductorExponent.SpectralConductorStatement.{uK, uW} K :=
    fun q _ K => SpectralConductor.spectralConductorRankOneReduction.{uK, uW} K
      (fun A => Ramification.Padic.finiteInertiaConductorRefinement K A)
      (SpectralConductor.commonClosureRankOneConductor q K)
  have hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} :=
    RankinSelberg.pairEpsilonExponentReduction
      RankinSelberg.equalRankEpsilonCharacterChange.{uK, uV, 0}
  have hJPSS := Conductor.supercuspidalPadicConductorExponent.{uK, uV}
  have hfin := Extension.SupercuspidalConductor.supercuspidalEpsilonConductorFiniteness_of_pairEpsilon
    hBHK hJPSS
  have hUTI := Extension.unramifiedTwistIndependence_of_reciprocity hCE hrec
  -- the candidate is a numerical injection wherever it is defined
  have hinj : ∀ {q : ℕ} [Fact q.Prime] (K : PadicField.{uK} q) {k : ℕ}
      (hS : StableExistsAt.{uK, uW, uV, uW} K k.succPNat),
      IsNumericalInjection K (Extension.rankExtension K hS) := by
    intro q _ K k hS
    obtain ⟨eC, heC⟩ := hrec q K K.canonicalTopologicalData
    have he := baseGeometricReciprocityProof K eC heC
    obtain ⟨ε, hε⟩ := hsys q K eC heC
    exact ⟨Extension.rankExtension_injective K hS hCE he,
      fun σ a ha => Extension.SupercuspidalConductor.rankExtension_conductor K (hSC q K) hBHK
        hJPSS he hε hS σ ha,
      fun z σ => Extension.rankExtension_twist K hS hUTI z σ⟩
  -- stable existence in the ranks at most `N`
  have hstab : ∀ {q : ℕ} [Fact q.Prime] (K : PadicField.{uK} q) (n : ℕ+), (n : ℕ) ≤ N →
      StableExistsAt.{uK, uW, uV, uW} K n := by
    intro q _ K n
    refine PNat.strongInductionOn
      (p := fun n : ℕ+ => (n : ℕ) ≤ N → StableExistsAt.{uK, uW, uV, uW} K n) n
      (fun n ih => ?_)
    intro hn
    by_cases h1 : n = 1
    · subst h1
      exact (Extension.rankOneStage_of_reciprocity hCE hrec q K).1
    · have hlt : 1 < n := lt_of_le_of_ne (one_le : 1 ≤ n) (Ne.symm h1)
      refine Extension.choiceIndependenceStep_of_inputs hCE hfin hrec hsys q K n hlt ?_
      intro r hr
      have hrN : (r : ℕ) < N := lt_of_lt_of_le hr hn
      have hSr : StableExistsAt.{uK, uW, uV, uW} K r := ih r hr hrN.le
      refine ⟨hSr, ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, k.succPNat = r := ⟨r.natPred, PNat.succPNat_natPred r⟩
      obtain ⟨eC, heC⟩ := hrec q K K.canonicalTopologicalData
      have he := baseGeometricReciprocityProof K eC heC
      exact Extension.stableSurjectiveAt_of_surjective K hSr hCE he
        (hsurj q K k (by simpa using hrN) _ (hinj K hSr))
  obtain ⟨Ch, hW, hCI1, hCI2⟩ := hBC p S
  have hk : ∀ {k : ℕ}, k + 1 ≤ N → ((k.succPNat : ℕ+) : ℕ) ≤ N := fun h => by simpa using h
  refine ⟨fun k hk' => Extension.rankExtension S.base (hstab S.base k.succPNat (hk hk')),
    fun k hk' => Extension.rankExtension S.top (hstab S.top k.succPNat (hk hk')), Ch,
    fun k hk' => ⟨hinj S.base _, hinj S.top _⟩, hW, ?_, ?_⟩
  · intro k hk' σ m hm hmN
    rw [hCI1 k _ σ m hm (fun τ hτ => hstab S.top τ.1.succPNat (hk (hmN τ hτ)))]
    exact Multiset.pmap_congr m (fun _ _ _ _ => rfl)
  · intro k hk' τ hfix w
    obtain ⟨eC, heC⟩ := hrec p S.top S.top.canonicalTopologicalData
    have he := baseGeometricReciprocityProof S.top eC heC
    apply Extension.rankExtension_injective S.top (hstab S.top k.succPNat (hk hk')) hCE he
    rw [hCI2 k _ w τ]
    exact hfix _

end Langlands.Henniart
