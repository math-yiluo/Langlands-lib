import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: central maximal tori in nilpotent group varieties -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine nilpotent group has a central maximal torus and an
actual affine unipotent fppf quotient by that torus. -/
def NilpotentCentralTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsNilpotentGroupScheme G →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
        (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        IsMaximalTorus i ∧ IsCentral i ∧ IsAffineHom Q.X.hom ∧ IsUnipotent Q ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q

end Langlands.GroupScheme
