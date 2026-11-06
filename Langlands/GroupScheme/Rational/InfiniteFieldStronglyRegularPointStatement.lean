import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: rational points with torus centralizer over infinite fields -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Strongly regular rational points over infinite fields.** Every connected reductive
group scheme `H` over an infinite field `K` has a rational point `x` and a closed torus
`i : T ⟶ H` over `K` such that every point of `H` on any test commuting with `x` factors
through `T`: the all-test centralizer of `x` is contained in (hence equal to) `T`. -/
def InfiniteFieldStronglyRegularPointStatement : Prop :=
  ∀ (K : Type u) [Field K] [Infinite K]
    (H : GroupScheme (Spec (CommRingCat.of K))),
    IsConnectedReductive H →
    ∃ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X)
      (T : GroupScheme (Spec (CommRingCat.of K))) (i : T ⟶ H),
      IsTorus T ∧ IsClosedSubgroup i ∧
        ∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ H.X),
          c * (toUnit Z ≫ x) = (toUnit Z ≫ x) * c →
            ∃ t : Z ⟶ T.X, t ≫ i.hom.hom = c

end Langlands.GroupScheme
