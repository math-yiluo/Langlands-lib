import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # The pseudo-reductive quotient by a ground-field unipotent radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every represented ground-field unipotent radical of a smooth connected
affine group scheme admits a represented fppf quotient which is pseudo-reductive.
This declaration is a proposition target. -/
def UnipotentRadicalQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      IsUnipotentRadical i →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
          IsPseudoReductive Q

end Langlands.GroupScheme
