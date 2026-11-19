import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A torus has a point with the same centralizer (Milne 16.42) -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Lemma 16.42: let `G` be a smooth connected affine group over an algebraically
closed field `k` and let `j : T ⟶ G` be a torus in `G`. There is a rational point `s` of `T` such
that the centralizer of `s` in `G` equals the centralizer of `T`, as subgroup functors on all
test schemes. -/
def TorusGenericPointCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsClosedSubgroup j → IsTorus T.toGrp →
      ∃ s : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ T.X,
        G.pointCentralizer (s ≫ j.hom.hom) = torusCentralizer j

end Langlands.GroupScheme
