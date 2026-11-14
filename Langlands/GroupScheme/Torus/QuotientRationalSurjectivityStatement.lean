import Langlands.GroupScheme.Rational.TorusCocycleVanishing
import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.Rational.Characters

/-! # Rational surjectivity of torus quotients with torus kernel -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Rational points of a quotient of tori with torus kernel.**
Over a field on which every torus cocycle on a finite Galois cover is a
coboundary, a homomorphism of tori whose underlying scheme map is surjective
and whose scheme-theoretic kernel is a torus is surjective on rational points. -/
def TorusQuotientRationalSurjectivityStatement : Prop :=
  ∀ (k : Type u) [Field k], HasTrivialTorusCocycles k →
    ∀ (B C : GroupScheme (Spec (CommRingCat.of k))),
      IsTorus B → IsTorus C →
      ∀ q : B ⟶ C,
        Surjective q.hom.hom.left → IsTorus (kernel q) →
          Function.Surjective (rationalPoints.map q)

end Langlands.GroupScheme
