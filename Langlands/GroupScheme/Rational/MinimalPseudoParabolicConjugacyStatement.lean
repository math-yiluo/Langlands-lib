import Langlands.GroupScheme.Rational.MinimalPseudoParabolic
import Langlands.GroupScheme.Rational.SubgroupConjugacy

/-! # Rational conjugacy of minimal pseudo-parabolic subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Minimal pseudo-parabolic subgroups of a smooth connected affine group over
an arbitrary field are conjugate by an actual ground-field rational point. -/
def MinimalPseudoParabolicConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → ConnectedSpace G.X.left → IsAffineHom G.X.hom →
    ∀ (P Q : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G) (j : Q ⟶ G),
      IsMinimalPseudoParabolicSubgroup i → IsMinimalPseudoParabolicSubgroup j →
        SubgroupConjugate i j

end Langlands.GroupScheme
