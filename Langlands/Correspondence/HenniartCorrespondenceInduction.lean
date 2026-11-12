import Langlands.Correspondence.HenniartCorrespondenceRemaining
import Langlands.Correspondence.HenniartRankOneStageProof
import Langlands.Correspondence.HenniartChoiceIndependenceStepProof

/-!
# Henniart's route with the rank induction carried out

Henniart (2000), §4.3. The rank induction is proved from its three parts: the
rank-one stage, the inductive step for stable images, and the surjectivity step.
The rank-one stage and the inductive step are proved here from candidate
existence, local reciprocity, local constants and the conductor finiteness of
candidate sets. So the published `StableCorrespondenceStatement` hypothesis of
`SupercuspidalCorrespondenceHenniartRemainingStatement` is replaced by
`SurjectivityStepStatement` and `SupercuspidalEpsilonConductorFinitenessStatement`.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open LocalFactor LocalFactor.CommonClosure

universe uK uW uV uE

/-- Henniart (2000), §4.3: the rank-one stage, the inductive step for stable
images and the surjectivity step give both assertions of 4.2 in every rank, by
strong induction on the rank. -/
theorem stableCorrespondence_of_steps (hone : RankOneStageStatement.{uK, uW, uV, uE})
    (hstep : ChoiceIndependenceStepStatement.{uK, uW, uV, uE})
    (hsurj : SurjectivityStepStatement.{uK, uW, uV, uE}) :
    StableCorrespondenceStatement.{uK, uW, uV, uE} := by
  intro p _ K n
  induction n using PNat.strongInductionOn with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn
    · exact hone p K
    · have hlt : 1 < n := lt_of_le_of_ne (one_le : (1 : ℕ+) ≤ n) (Ne.symm hn)
      have hex := hstep p K n hlt ih
      exact ⟨hex, hsurj p K n hex⟩

/-- Henniart's route to the all-field supercuspidal correspondence with the rank
induction carried out: candidate existence, the surjectivity step, the conductor
finiteness of candidate sets, normalized local reciprocity and local constants
for every normalized family give the correspondence. -/
def SupercuspidalCorrespondenceHenniartInductionStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  SurjectivityStepStatement.{uK, uW, uV, uW} →
  SupercuspidalEpsilonConductorFinitenessStatement.{uK, uV} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

theorem supercuspidalCorrespondenceHenniartInduction :
    SupercuspidalCorrespondenceHenniartInductionStatement.{uK, uW, uV} := by
  intro hCE hsurj hfinite hrec hsys
  exact supercuspidalCorrespondenceHenniartRemaining hCE
    (stableCorrespondence_of_steps (rankOneStage_of_reciprocity hCE hrec)
      (choiceIndependenceStep_of_inputs hCE hfinite hrec hsys) hsurj)
    hrec hsys

end Langlands.Henniart.Extension
