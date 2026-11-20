import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.MultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A Borel subgroup is the normalizer of its unipotent part on rational points (Milne 17.50) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 17.50, on rational points over an algebraically closed field: let
`i : B ⟶ G` be a Borel subgroup of a smooth connected affine group `G`, and let `u : U ⟶ B` be
a closed normal unipotent subgroup of `B` with an fppf quotient `q : B ⟶ Q` of multiplicative
type (the subgroup `B_u` of Milne's Notation 16.7). Then the normalizer in `G(k)` of the image
of `U(k)` is the image of `B(k)`. The scheme-theoretic form `B = N_G(B_u)` fails for `PGL_2` in
characteristic `2`; see the Markdown. -/
def BorelUnipotentNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B U Q : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (u : U ⟶ B) (q : B ⟶ Q),
    IsBorelSubgroup i → IsClosedSubgroup u → IsUnipotent U →
      (SubgroupFunctor.range u).IsNormal →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range u) q → IsMultiplicativeType Q →
        Subgroup.normalizer
            ((SubgroupFunctor.range (u ≫ i)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
              Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
          (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))

end Langlands.GroupScheme
