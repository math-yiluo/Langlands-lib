import Langlands.Global.ArchimedeanCompact
import Mathlib.Topology.Connected.Basic

/-! # Compact representatives of archimedean connected components -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- The actual standard orthogonal/unitary compact subgroup meets every
connected component of the actual archimedean general linear group. -/
def CompactComponentCoverageStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K),
    ∃ k : standardInfiniteCompact K n, g ∈ connectedComponent k.val

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactComponentCoverageStatement

end Langlands.Global.ArchimedeanGL
