import Langlands.GroupScheme.Rational.RealAnisotropicMaximalTorusConjugacyStatement
import Langlands.GroupScheme.Rational.PointTopology

/-! # Maximal-torus conjugacy for compact real semisimple groups -/

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Maximal tori of a real semisimple group whose actual real points are compact
are conjugate by a real point, as full subgroup functors. This is a statement
target for the compact-form theorem of Cartan. -/
def RealCompactMaximalTorusConjugacyStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) (hG : IsSemisimple G),
    letI : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology ℝ G.X
    IsCompact (Set.univ : Set (rationalPoints G)) →
      ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of ℝ))) (j : T.toGrp ⟶ G)
        (j' : T'.toGrp ⟶ G), IsMaximalTorus j → IsMaximalTorus j' →
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of ℝ))) ⟶ G.X,
            SubgroupFunctor.range (j ≫ (G.innerIso g).hom) = SubgroupFunctor.range j'

end Langlands.GroupScheme
