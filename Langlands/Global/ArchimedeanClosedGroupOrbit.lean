import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Representation.FiniteVectors

/-! # The actual closed full group orbit submodule -/

noncomputable section
universe u
open Set
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The closed complex span of all actual right translates of one smooth vector. -/
def closedGroupOrbitSpan (f : DerivativeSmoothFunctions K n) :
    Submodule ℂ (DerivativeSmoothFunctions K n) :=
  (Submodule.span ℂ (range fun g : InfiniteAdelicGL K n =>
    rightAction K n g f)).topologicalClosure

theorem isClosed_closedGroupOrbitSpan (f : DerivativeSmoothFunctions K n) :
    IsClosed (closedGroupOrbitSpan K n f : Set (DerivativeSmoothFunctions K n)) :=
  Submodule.isClosed_topologicalClosure _

theorem rightAction_mem_closedGroupOrbitSpan (f : DerivativeSmoothFunctions K n)
    (g : InfiniteAdelicGL K n) :
    rightAction K n g f ∈ closedGroupOrbitSpan K n f :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, rfl⟩)

theorem self_mem_closedGroupOrbitSpan (f : DerivativeSmoothFunctions K n) :
    f ∈ closedGroupOrbitSpan K n f := by
  simpa using rightAction_mem_closedGroupOrbitSpan K n f 1

/-- Each actual continuous right translation preserves the closed full orbit span. -/
theorem rightAction_mem_closedGroupOrbitSpan_of_mem
    (f : DerivativeSmoothFunctions K n) (g : InfiniteAdelicGL K n)
    {w : DerivativeSmoothFunctions K n} (hw : w ∈ closedGroupOrbitSpan K n f) :
    rightAction K n g w ∈ closedGroupOrbitSpan K n f := by
  let S := Submodule.span ℂ (range fun h : InfiniteAdelicGL K n =>
    rightAction K n h f)
  have hle : S ≤ (closedGroupOrbitSpan K n f).comap (rightAction K n g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    change rightAction K n g (rightAction K n h f) ∈ closedGroupOrbitSpan K n f
    rw [← Module.End.mul_apply, ← map_mul]
    exact rightAction_mem_closedGroupOrbitSpan K n f (g * h)
  have hclosed : IsClosed
      ((closedGroupOrbitSpan K n f).comap (rightAction K n g) :
        Set (DerivativeSmoothFunctions K n)) :=
    (isClosed_closedGroupOrbitSpan K n f).preimage
      (continuous_rightAction_apply K n g)
  exact S.topologicalClosure_minimal hle hclosed hw

/-- A vector in this closed invariant submodule generates no larger closed orbit. -/
theorem closedGroupOrbitSpan_le_of_mem
    (f : DerivativeSmoothFunctions K n) {w : DerivativeSmoothFunctions K n}
    (hw : w ∈ closedGroupOrbitSpan K n f) :
    closedGroupOrbitSpan K n w ≤ closedGroupOrbitSpan K n f := by
  refine (Submodule.span ℂ (range fun g : InfiniteAdelicGL K n =>
    rightAction K n g w)).topologicalClosure_minimal ?_
      (isClosed_closedGroupOrbitSpan K n f)
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact rightAction_mem_closedGroupOrbitSpan_of_mem K n f g hw

/-- The original compact orbit span is contained in the closed full group orbit. -/
theorem compactOrbitSpan_le_closedGroupOrbitSpan
    (f : DerivativeSmoothFunctions K n) :
    Langlands.FiniteVectors.orbitSpan (compactAction K n) f ≤
      closedGroupOrbitSpan K n f := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact rightAction_mem_closedGroupOrbitSpan K n f k.val

end Langlands.Global.ArchimedeanGL
