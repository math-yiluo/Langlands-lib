import Langlands.Correspondence.HenniartSupercuspidalConductorReductionStatement
import Langlands.Correspondence.HenniartSupercuspidalConductorSurjectivity
import Langlands.Correspondence.HenniartCorrespondenceInduction
import Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeProof
import Langlands.Representation.RankinSelberg.PairEpsilonExponentProof
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.LocalFactor.SpectralConductorReduction
import Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof
import Langlands.LocalFactor.NonabelianSystemExistsProof
import Langlands.LocalFactor.SpectralConductorRankOneProof

/-!
# Henniart's three-input route with the supercuspidal p-adic conductor premise

Candidate existence, numerical surjectivity and the conductor theorem for
supercuspidal p-adic representations imply the supercuspidal correspondence.
All field, Weil-carrier and representation universes are independent.
-/

namespace Langlands.Henniart.Extension

open Langlands.Correspondence LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart's three-input route requires the conductor theorem only for
supercuspidal representations over p-adic fields. -/
theorem supercuspidalCorrespondenceHenniartSupercuspidalConductor :
    SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement.{uK, uW, uV} := by
  intro hCE hnum hC
  have hrec := LocalClassField.commonClosureReciprocityExistence.{uK}
  have hsys : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
      NonabelianSystem.Exists.{uK, uW} K eC :=
    fun _ _ K eC => NonabelianSystem.exists_system K eC
  have hSC : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p),
      ConductorExponent.SpectralConductorStatement.{uK, uW} K :=
    fun p _ K => SpectralConductor.spectralConductorRankOneReduction.{uK, uW} K
      (fun A => Ramification.Padic.finiteInertiaConductorRefinement K A)
      (SpectralConductor.commonClosureRankOneConductor p K)
  have hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} :=
    RankinSelberg.pairEpsilonExponentReduction
      RankinSelberg.equalRankEpsilonCharacterChange.{uK, uV, 0}
  exact supercuspidalCorrespondenceHenniartInduction hCE
    (SupercuspidalConductor.surjectivityStepReduction hCE hrec hsys hnum hSC hBHK hC)
    (SupercuspidalConductor.supercuspidalEpsilonConductorFiniteness_of_pairEpsilon hBHK hC)
    hrec hsys

end Langlands.Henniart.Extension
