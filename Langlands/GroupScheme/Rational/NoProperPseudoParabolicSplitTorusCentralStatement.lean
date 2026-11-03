import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.Characters

/-! # Split tori become central modulo the radical without proper pseudo-parabolics

This is a statement derived from CGP Lemma 2.2.3. No proof is supplied.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- If a smooth connected affine group over a field has no proper
pseudo-parabolic subgroup, then every split subtorus maps centrally into every
represented fppf quotient by a ground-field unipotent radical that is
pseudo-reductive. -/
def NoProperPseudoParabolicSplitTorusCentralStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom],
    (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsPseudoParabolicSubgroup i → IsIso i) →
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ G),
      IsUnipotentRadical r →
    ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q → IsPseudoReductive Q →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsSplitSubtorus i → IsCentral (i ≫ q)

end Langlands.GroupScheme
