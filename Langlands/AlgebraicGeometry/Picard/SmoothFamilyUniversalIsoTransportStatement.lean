import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement

/-! # Universal smooth-family transport along an abelian-scheme isomorphism -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A universal smooth-family rigidified family transports along an abelian-scheme
isomorphism while keeping its parameter scheme. -/
def SmoothFamilyUniversalIsoTransportStatement : Prop :=
  ∀ (S : Scheme.{u}) (A A' : AbelianScheme S) (_ : A ≅ A')
    (P : Over S) (L : RigidifiedFamily A' P),
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A' L →
      ∃ L' : RigidifiedFamily A P, IsUniversalSmoothFamilyOnQuasiSeparatedTests A L'

end Langlands.AbelianScheme
