import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting
import Langlands.AbelianScheme.TrivialPullbackCharacterInjective
import Langlands.AbelianScheme.TrivialPullbackCharacterInjectiveStatement
import Langlands.AlgebraicGeometry.Picard.TrivialPullbackTranslationInvariance
import Langlands.AlgebraicGeometry.Picard.TrivialHomPullbackGeometricFibres

/-! # Geometric Picard zero from trivial field-isogeny pullback -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The algebraically closed field criterion, from injectivity of the class character. -/
theorem algClosedFieldTrivialPullbackTranslationInvariant_of
    (hinj : TrivialPullbackCharacterInjectiveStatement.{u}) :
    AlgClosedFieldTrivialPullbackTranslationInvariantStatement.{u} := by
  intro K _ _ A B f hf L hL
  exact isTranslationInvariant_of_trivialHomPullback f
    (fun x => exists_point_lift_of_isogeny hf x) (hinj _ A B f hf _) L hL

theorem fieldTrivialPullbackPicardZero_of
    (hinj : TrivialPullbackCharacterInjectiveStatement.{u}) :
    FieldTrivialPullbackPicardZeroStatement.{u} :=
  fieldTrivialPullbackPicardZero_of_algClosed_translationInvariant
    (algClosedFieldTrivialPullbackTranslationInvariant_of hinj)

/-- A trivialized rigidified family over a field has geometric Picard-zero fibres. -/
theorem fieldTrivialPullbackPicardZero : FieldTrivialPullbackPicardZeroStatement.{u} :=
  fieldTrivialPullbackPicardZero_of trivialPullbackCharacterInjective

end Langlands.AbelianScheme
