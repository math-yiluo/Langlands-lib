import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.Torus.TwistedTransporter
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Statement: rank-one reductivity from an actual Weyl inversion -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The rank-one field input for the reductivity-locus argument. The Weyl
element and its action are supplied as an actual all-test transporter. -/
def RankOneWeylReductivityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsSplitSubtorus i →
    torusCentralizer i = SubgroupFunctor.range i →
    ∀ (α : characterLattice T), α ≠ 0 →
      (∀ β : characterLattice T, β ∈ roots i ↔ β = α ∨ β = -α) →
      Module.finrank k (weightSpace i α) = 1 →
      Module.finrank k (weightSpace i (-α)) = 1 →
      ∀ (c : T.toGrp ≅ T.toGrp) (n : Lie.AffinePoints G k),
        c.hom ≫ CommGroupScheme.groupHom α = CommGroupScheme.groupHom (-α) →
        PointwiseSchemeAction.IsTransporter (c.hom ≫ i) i n →
        IsConnectedReductive G

end Langlands.GroupScheme
