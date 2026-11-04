import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic

/-! # Rational points of dynamic unipotent subgroups in unipotent normal subgroups

This module states a generalization of the rational-point step in the proof of CGP
Proposition C.1.6 for a pseudo-reductive group. It supplies no proof.
-/

universe u

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Let `G` be pseudo-reductive over `k`, let `χ` be a cocharacter, and let `H` be a
closed unipotent normal subgroup of the base change of `G` to a field extension
`K`. A rational point `u` of `U_G(χ)` whose base change to `K` lies in `H` is
trivial. -/
def PseudoReductiveRationalUnipotentPointStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsPseudoReductive G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (H : GroupScheme (Spec (CommRingCat.of K)))
      (j : H ⟶ (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G),
      IsClosedSubgroup j → IsUnipotent H → (SubgroupFunctor.range j).IsNormal →
      ∀ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        u ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) →
        (∃ y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X,
          baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G
              (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (y ≫ j.hom.hom) =
            toUnit _ ≫ u) →
        u = 1

end Langlands.GroupScheme
