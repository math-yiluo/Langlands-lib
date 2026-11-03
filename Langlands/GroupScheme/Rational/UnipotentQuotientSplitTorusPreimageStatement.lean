import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Absolute.Borel

/-! # The preimage of a split subtorus under a quotient by a unipotent subgroup

This is a statement derived from the proof of CGP Theorem C.2.3. No proof is
supplied.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For a represented fppf quotient `q : G ⟶ Q` of a smooth connected affine
group by a smooth connected unipotent closed subgroup, and a split subtorus
`z : B ⟶ Q`, some smooth connected affine solvable closed subgroup of `G`
receives every homomorphism whose composite with `q` factors through `z`. -/
def UnipotentQuotientSplitTorusPreimageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ G),
    IsClosedSubgroup r → Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
    ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q →
    ∀ (B : CommGroupScheme (Spec (CommRingCat.of k))) (z : B.toGrp ⟶ Q),
      IsSplitSubtorus z →
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
      IsClosedSubgroup j ∧
      Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧ IsAffineHom H.X.hom ∧
      IsSolvableGroupScheme H ∧
      ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (i : K ⟶ G) (g : K ⟶ B.toGrp),
        g ≫ z = i ≫ q → ∃ f : K ⟶ H, f ≫ j = i

end Langlands.GroupScheme
