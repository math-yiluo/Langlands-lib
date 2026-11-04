import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Fppf image factorization of homomorphisms of affine algebraic groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne's homomorphism theorem for affine algebraic groups over a field: every
actual homomorphism `f : G ⟶ H` of affine group schemes locally of finite type
over `Spec k` factors as `q ≫ i = f` through an actual affine group scheme `I`
locally of finite type. Here `i` is a closed subgroup inclusion and `q` is a
represented fppf quotient of `G` by the full actual kernel of `f`. There is no
smoothness or connectedness premise. -/
def AffineHomImageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom] (f : G ⟶ H),
    ∃ (I : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ I) (i : I ⟶ H),
      LocallyOfFiniteType I.X.hom ∧ IsAffineHom I.X.hom ∧
        IsClosedSubgroup i ∧ q ≫ i = f ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q

end Langlands.GroupScheme
