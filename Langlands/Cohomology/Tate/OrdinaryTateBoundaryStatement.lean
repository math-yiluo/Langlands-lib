import Langlands.Cohomology.Tate.OrdinaryTateComparison
import Langlands.Cohomology.Tate.BoundaryDiagrams
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

/-- The canonical comparison preserves cocycle representatives and connecting maps. -/
def OrdinaryTateBoundaryLaws : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G] [Fintype G],
    (∀ (A : Rep.{u} R G) (n : ℕ)
      (z : (groupCohomology.inhomogeneousCochains A).X n)
      (hz : (groupCohomology.inhomogeneousCochains A).d n (n + 1) z = 0),
      ordinaryToTate A n ((groupCohomology.inhomogeneousCochains A).homologyπ n
        ((groupCohomology.inhomogeneousCochains A).cyclesMk z (n + 1) (by simp) hz)) =
        cycleClass (tateComplex A) n z hz) ∧
    (∀ (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact) (n : ℕ),
      groupCohomology.δ hS n (n + 1) rfl ≫ ordinaryToTate S.X₁ (n + 1) =
        ordinaryToTate S.X₃ n ≫ TateCohomology.δ hS n)

end Langlands.Tate
