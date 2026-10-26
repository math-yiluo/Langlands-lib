import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAlgebraicTriviality
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Smooth-family representability on quasi-separated tests -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- An actual smooth-family algebraically trivial rigidified family classifies
every smooth-family algebraically trivial class on a quasi-separated test.
The parameter scheme is unrestricted. -/
def IsUniversalSmoothFamilyOnQuasiSeparatedTests {P : Over S}
    (L : RigidifiedFamily A P) : Prop :=
  IsAlgebraicallyTrivialFamilyViaSmoothFamily A L ∧
    ∀ (T : Over S) [QuasiSeparatedSpace T.left]
      (q : AlgebraicallyTrivialClassesViaSmoothFamily A T),
      ∃! h : T ⟶ P,
        RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
          (unitSection_comp A) L T h = q.val

/-- Every abelian scheme over a quasi-separated base admits an actual universal
rigidified smooth-family algebraically trivial family on quasi-separated tests. -/
def SmoothFamilyQuasiSeparatedRepresentabilityStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S),
    ∃ (P : Over S) (L : RigidifiedFamily A P),
      IsUniversalSmoothFamilyOnQuasiSeparatedTests A L

end Langlands.AbelianScheme
