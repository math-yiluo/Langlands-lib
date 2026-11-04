import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Lie.DimensionInduction

/-! # Quotienting a Borel pair by a central multiplicative subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A central closed copy of Gm contained in a Borel can be quotiented out.
The quotient stays smooth, connected and affine, its Lie dimension decreases,
and the Borel descends with its exact all-test inverse image. -/
def CentralMultiplicativeQuotientBorelStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
    IsBorelSubgroup i →
    ∀ (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G),
      IsClosedSubgroup z → SubgroupFunctor.range z ≤ center G →
      ∀ (zB : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B), zB ≫ i = z →
        ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
          (hAffQ : IsAffineHom Q.X.hom),
          Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
          Smooth q.hom.hom.left ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q ∧
          (letI := hAffQ
           Lie.dimension Q < Lie.dimension G) ∧
          ∃ (BQ : GroupScheme (Spec (CommRingCat.of k))) (iQ : BQ ⟶ Q)
            (qB : B ⟶ BQ),
            IsBorelSubgroup iQ ∧ i ≫ q = qB ≫ iQ ∧
            Smooth qB.hom.hom.left ∧
            RelativeRoot.IsFppfQuotient (SubgroupFunctor.range zB) qB ∧
            (SubgroupFunctor.range iQ).comap q = SubgroupFunctor.range i

end Langlands.GroupScheme
