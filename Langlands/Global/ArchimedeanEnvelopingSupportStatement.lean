import Langlands.Global.ArchimedeanEnvelopingAction
import Mathlib.Topology.Algebra.Support

/-! # Support of the actual archimedean enveloping differential -/

noncomputable section
universe u

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Genuine enveloping differential operators do not enlarge topological support. -/
def EnvelopingSupportStatement : Prop :=
  ∀ (a : EnvelopingAlgebra K n) (f : SmoothFunctions K n),
    tsupport (envelopingAction K n a f).val ⊆ tsupport f.val

/-- In particular a compact smooth kernel has compactly supported derivatives. -/
def EnvelopingCompactSupportStatement : Prop :=
  ∀ (a : EnvelopingAlgebra K n) (f : SmoothFunctions K n),
    HasCompactSupport f.val → HasCompactSupport (envelopingAction K n a f).val

theorem envelopingCompactSupport_of_support (h : EnvelopingSupportStatement K n) :
    EnvelopingCompactSupportStatement K n := by
  intro a f hf
  exact hf.of_isClosed_subset (isClosed_tsupport _) (h a f)

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @EnvelopingSupportStatement

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @EnvelopingCompactSupportStatement

end Langlands.Global.ArchimedeanGL
