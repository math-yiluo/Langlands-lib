import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement

/-! # Comparison of universal smooth-family parameters -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Two universal smooth-family algebraically trivial rigidified families on
quasi-separated tests, one of whose parameters is quasi-separated, have parameters
related by exactly one isomorphism over the base that pulls the second family back
to a family isomorphic to the first. The second parameter and the base are
unrestricted. -/
def SmoothFamilyUniversalComparisonStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (P Q : Over S) [QuasiSeparatedSpace P.left]
    (L : RigidifiedFamily A P) (M : RigidifiedFamily A Q),
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A L →
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A M →
    ∃! e : P ≅ Q,
      Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) e.hom).obj M ≅ L)

end Langlands.AbelianScheme
