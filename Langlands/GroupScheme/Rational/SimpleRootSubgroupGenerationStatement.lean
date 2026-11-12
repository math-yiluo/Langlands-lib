import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.SplitTorus

/-!
# Simple root subgroups and their opposites generate every root subgroup

Every subgroup functor of a connected reductive group which contains the root
subgroups of the simple relative roots and of their negatives contains every
relative root subgroup.
This module states a proposition and supplies no proof of it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over any field `k`, let `i : S ⟶ G` be a maximal split torus of a connected reductive
group `G` and `ν` a generic cocharacter of `S`. Every subgroup functor `F` of `G` containing
`RelativeRoot.subgroup i α` and `RelativeRoot.subgroup i (-α)` for every simple relative root
`α` contains `RelativeRoot.subgroup i a` for every relative root `a`. -/
def SimpleRootSubgroupGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ F : SubgroupFunctor G,
      (∀ α ∈ simpleRelativeRoots i ν,
        RelativeRoot.subgroup i α ≤ F ∧ RelativeRoot.subgroup i (-α) ≤ F) →
      ∀ a ∈ relativeRoots i, RelativeRoot.subgroup i a ≤ F

end Langlands.GroupScheme
