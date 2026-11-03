import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.PseudoComplete
import Langlands.GroupScheme.SplitSolvable

/-! # Split-solvable fixed points on pseudo-complete schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every action of a split-solvable group on a pseudo-complete scheme with
a rational point has an all-test fixed rational point (CGP, Proposition C.1.5). -/
def SplitSolvablePseudoCompleteFixedPointStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))),
    IsSplitSolvableGroupScheme H →
      ∀ (X : Over (Spec (CommRingCat.of k))),
        IsPseudoComplete X →
          Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) →
            ∀ (a : SchemeAction H X),
              ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed x

end Langlands.GroupScheme
