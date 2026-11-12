import Langlands.GroupScheme.Quaternionic.SpinCoverProperties
import Langlands.GroupScheme.Quaternionic.IsometrySplitRank

/-! # Split rank one for a supplied quaternionic spin cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {σ : FirstKindInvolution K D}
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n}
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}

/-- A supplied spin cover of a nondegenerate form of quadratic Witt index one
has split rank one. Its own definition supplies smoothness of the isometry group. -/
theorem IsSpinCover.splitRank_eq_one (hπ : σ.IsSpinCover q π)
    (hq : σ.IsNondegenerateQuadratic q) (hi : σ.quadraticWittIndex q = 1) :
    splitRank S = 1 := by
  let := hπ.smooth
  exact hπ.splitRank_eq.trans (σ.splitRank_connectedIsometryGroup_eq_one q hq hi)

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme.Quaternionic

/-- Over every infinite field, each supplied spin cover of a nondegenerate
quadratic form of Witt index one is simply connected and has split rank one. -/
def SpinCoverWittIndexOneStatement : Prop :=
  ∀ (K D : Type u) [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] (σ : FirstKindInvolution K D)
    (n : Type) [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n),
    σ.IsNondegenerateQuadratic q → σ.quadraticWittIndex q = 1 →
      ∀ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π → IsSimplyConnected S ∧ splitRank S = 1

theorem spinCoverWittIndexOne : SpinCoverWittIndexOneStatement.{u} := by
  intro K D _ _ _ _ _ σ n _ _ q hq hi S π hπ
  exact ⟨hπ.isSimplyConnected, hπ.splitRank_eq_one hq hi⟩

end Langlands.GroupScheme.Quaternionic
