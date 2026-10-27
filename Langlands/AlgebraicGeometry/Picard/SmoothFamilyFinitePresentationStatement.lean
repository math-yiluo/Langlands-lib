import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Local finite presentation of a universal smooth-family parameter -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the actual parameter scheme of every universal
rigidified smooth-family algebraically trivial family on quasi-separated tests is
locally of finite presentation over the base. The parameter is unrestricted. -/
def SmoothFamilyFinitePresentationStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S) (P : Over S)
    (L : RigidifiedFamily A P),
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A L →
      LocallyOfFinitePresentation P.hom

end Langlands.AbelianScheme
