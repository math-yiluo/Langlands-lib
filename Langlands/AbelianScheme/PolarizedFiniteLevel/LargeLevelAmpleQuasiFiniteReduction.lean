import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelAmpleStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelFiniteTypeStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelSeparatedStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiFiniteProjectiveStatement
import Langlands.AlgebraicGeometry.Picard.QuasiFiniteAmplePullbackStatement
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneAmpleProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure

/-! # Eventual ample line bundles from finite type, separatedness and a quasi-finite
projective map -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

set_option linter.defProp false in
/-- Proved definition: finite type, separatedness and a locally quasi-finite map to
projective space over `Spec ℤ[1/n]`, together with the general quasi-finite ample pullback
statement in universe zero, imply `LargeLevelAmpleStatement`. The ample line bundle is the
pullback of `𝒪(1)`. -/
def largeLevelAmple_of_quasiFiniteProjective
    (Hpull : Langlands.AlgebraicGeometry.Picard.QuasiFiniteAmplePullbackStatement.{0})
    (Hft : LargeLevelFiniteTypeStatement) (Hsep : LargeLevelSeparatedStatement)
    (Hqf : LargeLevelQuasiFiniteProjectiveStatement) :
    LargeLevelAmpleStatement := by
  intro P g d hg hd
  obtain ⟨N₁, hN₁⟩ := Hft P g d hg hd
  obtain ⟨N₂, hN₂⟩ := Hsep P g d hg hd
  obtain ⟨N₃, hN₃⟩ := Hqf P g d hg hd
  refine ⟨max N₁ (max N₂ N₃), fun n hn' hn X e => ?_⟩
  obtain ⟨hlft, hqc⟩ := hN₁ n (le_of_max_le_left hn') hn X e
  have hsep := hN₂ n (le_of_max_le_left (le_of_max_le_right hn')) hn X e
  obtain ⟨m, j, hjqf, hj⟩ := hN₃ n (le_of_max_le_right (le_of_max_le_right hn')) hn X e
  obtain ⟨M, -, hM⟩ :=
    Langlands.AlgebraicGeometry.projectiveSpaceTwistOneAmple (Localization.Away (n : ℤ)) m
  let p := Langlands.AlgebraicGeometry.projectiveSpaceToSpec (Localization.Away (n : ℤ)) m
  have : LocallyOfFiniteType (j ≫ p) := by rw [hj]; exact hlft
  have : QuasiCompact (j ≫ p) := by rw [hj]; exact hqc
  have : IsSeparated (j ≫ p) := by rw [hj]; exact hsep
  have : IsSeparated p := inferInstanceAs (IsSeparated
    (Langlands.AlgebraicGeometry.projectiveSpaceToSpec (Localization.Away (n : ℤ)) m))
  have : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j p
  have : QuasiCompact j := QuasiCompact.of_comp j p
  have : IsSeparated j := IsSeparated.of_comp j p
  exact ⟨hlft, _, Hpull X.obj _ j M inferInstance hjqf inferInstance inferInstance hM⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
