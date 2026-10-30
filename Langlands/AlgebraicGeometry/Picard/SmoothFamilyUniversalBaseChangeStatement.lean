import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.PoincareBaseChange

/-! # Base change of the actual universal smooth-family property -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- An actual universal smooth-family algebraically trivial family on
quasi-separated tests remains universal on quasi-separated tests after the
explicit simultaneous change of its parameter scheme and ground base. -/
def SmoothFamilyUniversalBaseChangeStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (A : AbelianScheme S) (P : Over S)
    (L : RigidifiedFamily A P), IsUniversalSmoothFamilyOnQuasiSeparatedTests A L →
      IsUniversalSmoothFamilyOnQuasiSeparatedTests ((baseChange b).obj A)
        ((baseChangeFamily b A P).obj L)

end Langlands.AbelianScheme
