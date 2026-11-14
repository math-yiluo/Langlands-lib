import Langlands.GroupScheme.ZExtension

/-! # Point surjectivity of quotients by induced central tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Rational-point surjectivity of an fppf quotient by an induced central torus:
for every field `k`, every field extension `K/k`, connected reductive `H` and `G`
over `k`, an induced torus `Z` with closed central inclusion `i : Z ⟶ H`, and a
homomorphism `p : H ⟶ G` that is an fppf quotient whose full scheme-theoretic
kernel is the image of `i` on every test, the induced map `H(K) → G(K)` is
surjective. -/
def InducedTorusQuotientPointSurjectivityStatement : Prop :=
  ∀ (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]
    (Z : CommGroupScheme (Spec (CommRingCat.of k)))
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (i : Z.toGrp ⟶ H) (p : H ⟶ G),
    IsInducedTorus Z → IsClosedSubgroup i → IsCentral i →
      IsConnectedReductive H → IsConnectedReductive G →
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p →
          Function.Surjective (H.affinePointsTarget p (CommAlgCat.of k K))

/-- The z-extension specialization: for every field `k`, every field extension
`K/k`, and every z-extension `1 → Z → H → G → 1` of a group `G` over `k`, the
induced map `H(K) → G(K)` is surjective. -/
def ZExtensionPointSurjectivityStatement : Prop :=
  ∀ (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) (z : ZExtension G),
      Function.Surjective (z.H.affinePointsTarget z.p (CommAlgCat.of k K))

/-- The z-extension specialization follows from the general induced-torus
statement, since every field of `IsZExtension` except the simply connected
derived group condition is one of its hypotheses. -/
theorem zExtensionPointSurjectivity_of_inducedTorusQuotient
    (h : InducedTorusQuotientPointSurjectivityStatement.{u}) :
    ZExtensionPointSurjectivityStatement.{u} := by
  intro k _ K _ _ G z
  exact h k K z.Z z.H G z.i z.p z.isZExtension.induced z.isZExtension.closed
    z.isZExtension.central z.isZExtension.source_reductive
    z.isZExtension.target_reductive z.isZExtension.quotient

end Langlands.GroupScheme
