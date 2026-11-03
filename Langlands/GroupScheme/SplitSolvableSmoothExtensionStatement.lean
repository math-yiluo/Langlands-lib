import Langlands.GroupScheme.SplitSolvable

/-! # Represented series through a smooth connected affine kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Represented Ga/Gm series join along an fppf quotient with a smooth
connected affine represented kernel. -/
def SmoothConnectedExtensionSeriesStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (N G Q : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G) (q : G ⟶ Q)
    [Mono i.hom.hom] [IsAffineHom G.X.hom]
    [Smooth N.X.hom] [IsAffineHom N.X.hom] [ConnectedSpace N.X.left]
    (n m : ℕ),
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
      SplitSolvable.HasSeries n N → SplitSolvable.HasSeries m Q →
        SplitSolvable.HasSeries (n + m) G

end Langlands.GroupScheme
