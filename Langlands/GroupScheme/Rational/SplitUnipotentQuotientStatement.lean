import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Langlands.GroupScheme.Absolute.Borel

/-! # Images and sections of split-unipotent quotients -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an arbitrary field, a locally finite-type group scheme that receives a
homomorphism from a smooth connected affine split unipotent group, surjective
as a map of fppf sheaves, is split unipotent. -/
def SplitUnipotentFppfQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (H Q : GroupScheme (Spec (CommRingCat.of k)))
    (φ : H ⟶ Q),
    IsAffineHom H.X.hom → LocallyOfFiniteType H.X.hom → Smooth H.X.hom →
    ConnectedSpace H.X.left → RelativeRoot.IsSplitUnipotent H →
    LocallyOfFiniteType Q.X.hom →
    (∀ (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ Q.X),
      ∃ (V : Over (Spec (CommRingCat.of k))) (v : V ⟶ T),
        Flat v.left ∧ Surjective v.left ∧ LocallyOfFinitePresentation v.left ∧
          ∃ x : V ⟶ H.X, x ≫ φ.hom.hom = v ≫ y) →
    RelativeRoot.IsSplitUnipotent Q

/-- The normal-subgroup case of Springer 14.2.6(i), expressed for an actual
represented fppf quotient. The section is a morphism over the field, with no
requirement that it preserve multiplication. -/
def SplitUnipotentQuotientSectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    ∀ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
    IsClosedSubgroup n → Smooth N.X.hom → ConnectedSpace N.X.left →
    IsUnipotent N → RelativeRoot.IsSplitUnipotent N →
    (SubgroupFunctor.range n).IsNormal →
    ∀ (Q : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth Q.X.hom] [IsAffineHom Q.X.hom] (q : G ⟶ Q),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q →
        ∃ s : Q.X ⟶ G.X, s ≫ q.hom.hom = 𝟙 Q.X

end Langlands.GroupScheme
