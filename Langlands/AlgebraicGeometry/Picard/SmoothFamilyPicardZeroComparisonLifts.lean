import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonStatement

/-! # Lifting the field smooth-family comparison to fibres, families and classes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The geometric-fibre lift: both predicates test the same actual fibre bundles. -/
theorem isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_field
    (h : SmoothFamilyTranslationInvarianceStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) (L : LineBundle A.X.left) :
    IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A L ↔ IsGeometricallyPicardZero A L :=
  forall_congr' fun K ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun s ↦
    h K ((baseChange s).obj A) (fibreLineBundle A L s)

/-- The rigidified-family lift, through the same actual `familyLineBundle`. -/
theorem isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_field
    (h : SmoothFamilyTranslationInvarianceStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) {T : Over S} (L : RigidifiedFamily A T) :
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A L ↔ IsPicardZeroFamily A L :=
  isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_field h _ (familyLineBundle A L)

/-- The rigidified-class lift, by induction on actual representatives. -/
theorem isAlgebraicallyTrivialClassViaSmoothFamily_iff_of_field
    (h : SmoothFamilyTranslationInvarianceStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) {T : Over S} (q : RigidifiedClasses A T) :
    IsAlgebraicallyTrivialClassViaSmoothFamily A q ↔ IsPicardZeroClass A q :=
  Quotient.inductionOn q fun L ↦ isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_field h A L

/-- The field comparison implies the full aggregate with its three lifts. -/
theorem smoothFamilyPicardZeroComparison_of_field
    (h : SmoothFamilyTranslationInvarianceStatement.{u}) :
    SmoothFamilyPicardZeroComparisonStatement.{u} :=
  ⟨h, fun _ A L ↦ isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_field h A L,
    fun _ A _ L ↦ isAlgebraicallyTrivialFamilyViaSmoothFamily_iff_of_field h A L,
    fun _ A _ q ↦ isAlgebraicallyTrivialClassViaSmoothFamily_iff_of_field h A q⟩

end Langlands.AbelianScheme
