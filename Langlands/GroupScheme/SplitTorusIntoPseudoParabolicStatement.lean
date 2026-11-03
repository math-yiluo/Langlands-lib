import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Rational conjugation of split subtori into pseudo-parabolic subgroups

This module states that every split subtorus of a smooth connected affine
group over a field can be conjugated by a rational point into any given
pseudo-parabolic subgroup. It does not prove the target.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field, every split subtorus `j` of a smooth connected affine group
`G` has a conjugate by a rational point `g` that factors through a given
pseudo-parabolic inclusion `i`. Here `innerIso g` acts by `x ↦ g x g⁻¹`. -/
def SplitTorusIntoPseudoParabolicStatement : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G), IsPseudoParabolicSubgroup i →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (j : S.toGrp ⟶ G),
        IsSplitSubtorus j →
          ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (f : S.toGrp ⟶ P),
            f ≫ i = j ≫ (G.innerIso g).hom

end Langlands.GroupScheme
