import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flatness of a universal smooth-family Picard parameter -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the parameter scheme of every actual universal
rigidified smooth-family algebraically trivial family on quasi-separated tests is
flat over the base. The parameter scheme is unrestricted. -/
def SmoothFamilyFlatStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S) (P : Over S)
    (L : RigidifiedFamily A P),
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A L → Flat P.hom

end Langlands.AbelianScheme
