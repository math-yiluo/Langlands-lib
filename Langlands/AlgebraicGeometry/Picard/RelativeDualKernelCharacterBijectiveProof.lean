import Langlands.AlgebraicGeometry.Picard.RelativeDualKernelCharacterBijectiveStatement
import Langlands.AlgebraicGeometry.Picard.DualKernelClassComparison
import Langlands.AlgebraicGeometry.Picard.FieldTrivialPullbackPicardZeroProof
import Langlands.AbelianScheme.FieldTrivialPullbackCharacterBijective

/-! # Relative bijectivity of the actual normalized dual-kernel character -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- A rigidified family with trivial isogeny pullback is Picard-zero over every base. -/
lemma relativeTrivialPullbackPicardZero {S : Scheme.{u}} {A B : AbelianScheme S}
    (f : A ⟶ B) (hf : IsIsogeny f) (T : Over S) (L : RigidifiedFamily B T)
    (hL : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L)) :
    IsPicardZeroFamily B L := by
  intro K _ _ s
  exact algClosedFieldTrivialPullbackTranslationInvariant_of trivialPullbackCharacterInjective
    K _ _ ((baseChange s).map ((baseChange T.hom).map f))
    ((hf.baseChange T.hom).baseChange s) _
    (homPullback_fibreLineBundle_trivial _ s _
      (homPullback_familyLineBundle_trivial f T L hL))

/-- The actual normalized relative dual-kernel character is bijective on every test scheme. -/
theorem relativeDualKernelCharacterBijective :
    RelativeDualKernelCharacterBijectiveStatement.{u} := by
  intro preservation composition unitCoherence associativity comparison symmetry stability
    S A B hA hB MA evaluationA MB evaluationB f hf T
  exact dualKernelPointCharacter_bijective_of_classification f hA stability hB
    preservation composition unitCoherence associativity comparison symmetry
    MA evaluationA MB evaluationB T
    (fun L hL => relativeTrivialPullbackPicardZero f hf T L hL)
    (trivialHomPullbackClassCharacter_bijective f hf T)

end Langlands.AbelianScheme
