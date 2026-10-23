import Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBundle

/-! # Uniqueness target for universal geometric Picard-zero bundles -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Two universal Picard-zero families admit a unique compatible isomorphism of their
parameter schemes. The bundle isomorphism is required to exist, not to be unique. -/
def PicardZeroUniversalUniquenessStatement : Prop :=
  Langlands.SchemeModule.RigidifiedModule.PullbackCoherenceStatement.{u} →
    ∀ (S : Scheme.{u}) (A : AbelianScheme S) (P Q : Over S)
      (L : RigidifiedFamily A P) (M : RigidifiedFamily A Q),
      IsUniversalPicardZero A L → IsUniversalPicardZero A M →
        ∃! e : P ≅ Q, Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom
          (unitSection A) (unitSection_comp A) e.hom).obj M ≅ L)

end Langlands.AbelianScheme
