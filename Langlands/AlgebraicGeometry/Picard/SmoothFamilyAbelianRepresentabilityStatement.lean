import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement

/-! # An abelian-scheme parameter for universal smooth-family classes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Every abelian scheme over a quasi-separated base admits an abelian-scheme
parameter carrying an actual universal rigidified smooth-family algebraically
trivial family on all quasi-separated tests. -/
def SmoothFamilyAbelianRepresentabilityStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S),
    ∃ (B : AbelianScheme S) (L : RigidifiedFamily A B.X),
      IsUniversalSmoothFamilyOnQuasiSeparatedTests A L

end Langlands.AbelianScheme
