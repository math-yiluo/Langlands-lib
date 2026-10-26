import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAlgebraicTriviality

/-! # Smooth-family algebraic triviality and translation invariance -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Over an algebraically closed field, the actual smooth-family condition
is equivalent to invariance under translation by every section. -/
def SmoothFamilyTranslationInvarianceStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left),
    IsAlgebraicallyTrivialViaSmoothFamily A L ↔
      Langlands.GroupScheme.IsTranslationInvariant A.toGrp L

/-- The field comparison and its geometric-fibre, rigidified-family, and
rigidified-isomorphism-class lifts, over arbitrary bases and tests. -/
def SmoothFamilyPicardZeroComparisonStatement : Prop :=
  SmoothFamilyTranslationInvarianceStatement.{u} ∧
    (∀ (S : Scheme.{u}) (A : AbelianScheme S) (L : LineBundle A.X.left),
      IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A L ↔
        IsGeometricallyPicardZero A L) ∧
    (∀ (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S)
      (L : RigidifiedFamily A T),
      IsAlgebraicallyTrivialFamilyViaSmoothFamily A L ↔ IsPicardZeroFamily A L) ∧
    (∀ (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S)
      (q : RigidifiedClasses A T),
      IsAlgebraicallyTrivialClassViaSmoothFamily A q ↔ IsPicardZeroClass A q)

end Langlands.AbelianScheme
