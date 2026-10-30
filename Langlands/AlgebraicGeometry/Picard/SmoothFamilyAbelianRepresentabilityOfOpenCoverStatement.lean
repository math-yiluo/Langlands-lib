import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityStatement
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Zariski-local existence of an abelian-scheme smooth-family representer -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- If, over every member of an open cover of a quasi-separated base, the
restricted abelian scheme admits an abelian-scheme parameter carrying an actual
universal rigidified smooth-family family on quasi-separated tests, then so does
the original abelian scheme over the whole base. -/
def SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (𝒰 : S.OpenCover.{u}),
    (∀ i, ∃ (B : AbelianScheme (𝒰.X i))
        (L : RigidifiedFamily ((baseChange (𝒰.f i)).obj A) B.X),
        IsUniversalSmoothFamilyOnQuasiSeparatedTests ((baseChange (𝒰.f i)).obj A) L) →
      ∃ (B : AbelianScheme S) (L : RigidifiedFamily A B.X),
        IsUniversalSmoothFamilyOnQuasiSeparatedTests A L

end Langlands.AbelianScheme
