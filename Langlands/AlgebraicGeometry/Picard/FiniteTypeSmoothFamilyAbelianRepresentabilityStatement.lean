import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement
import Mathlib.RingTheory.FiniteType

/-! # The smooth-family representer over affine bases of finite type over `ℤ` -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Every abelian scheme over `Spec R`, for a commutative ring `R` of finite type over `ℤ`,
admits an abelian-scheme parameter carrying an actual universal rigidified smooth-family
algebraically trivial family on all quasi-separated tests. -/
def FiniteTypeSmoothFamilyAbelianRepresentabilityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (A : AbelianScheme (Spec (CommRingCat.of R))),
    ∃ (B : AbelianScheme (Spec (CommRingCat.of R))) (L : RigidifiedFamily A B.X),
      IsUniversalSmoothFamilyOnQuasiSeparatedTests A L

end Langlands.AbelianScheme
