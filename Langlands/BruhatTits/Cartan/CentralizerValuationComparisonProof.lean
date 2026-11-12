import Langlands.BruhatTits.Cartan.ActualCentralizerStructureProof
import Langlands.BruhatTits.Cartan.CentralizerRealComparison
import Langlands.BruhatTits.Cartan.CentralizerValuationStatement
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective

/-! # Real comparison for the actual centralizer of a maximal split torus -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G} {j : Z ⟶ G}

/-- Restriction of rational characters from the represented centralizer of a maximal split torus
to that torus is injective and has finite-index range. -/
theorem characterRestrict_injective_finiteIndex_of_torusCentralizer (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hj : IsClosedSubgroup j)
    (hZ : (torusCentralizer i).IsRepresentedBy j) {s : S.toGrp ⟶ Z} (hs : s ≫ j = i) :
    Function.Injective (characterRestrict s) ∧ (characterRestrict s).range.FiniteIndex := by
  obtain ⟨hZred, hsplit⟩ := actualCentralizerStructure F G hG S i hi Z j hj hZ s hs
  exact ⟨characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter
      hZred hsplit, hsplit.finiteIndex_range_characterRestrict hZred⟩

/-- Over every field, restriction evaluation `V(S) → Hom(X^*(Z), ℝ)` is bijective for the
represented centralizer `Z` of a maximal split torus `S` of a connected reductive group. -/
theorem restrictionEvaluation_bijective_of_torusCentralizer (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hj : IsClosedSubgroup j)
    (hZ : (torusCentralizer i).IsRepresentedBy j) {s : S.toGrp ⟶ Z} (hs : s ≫ j = i) :
    Function.Bijective (restrictionEvaluation s) := by
  obtain ⟨hinj, hfin⟩ := characterRestrict_injective_finiteIndex_of_torusCentralizer hG hi hj hZ hs
  exact restrictionEvaluation_bijective hi.1.1 s hinj

/-- **Real comparison for the actual centralizer.** Over every nonarchimedean local field, for
the represented centralizer `Z` of a maximal split torus `S` of a connected reductive group,
restriction evaluation `V(S) → Hom(X^*(Z), ℝ)` is bijective. -/
theorem centralizerValuationComparison : CentralizerValuationComparisonStatement.{u} :=
  fun _ _ _ _ _ _ hG _ _ hi _ _ hj hZ _ hs =>
    restrictionEvaluation_bijective_of_torusCentralizer hG hi hj hZ hs

end Langlands.BruhatTits.Cartan
