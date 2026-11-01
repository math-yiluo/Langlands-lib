import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Representation.FiniteVectors

/-! # Closure transfer for actual compact-type intersections -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Taking the closure of a compact-finite invariant submodule adds no vectors
of a compact type whose intersection with the submodule is finite-dimensional. -/
def CompactTypeClosureTransferStatement : Prop :=
  ∀ (M : Submodule ℂ (DerivativeSmoothFunctions K n)),
    (∀ (k : standardInfiniteCompact K n) f,
      f ∈ M → compactAction K n k f ∈ M) →
    (∀ f, f ∈ M →
      Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f) →
    ∀ σ : CompactType K n,
      Module.Finite ℂ (M ⊓ compactTypeSubmodule σ :
        Submodule ℂ (DerivativeSmoothFunctions K n)) →
      M.topologicalClosure ⊓ compactTypeSubmodule σ =
        M ⊓ compactTypeSubmodule σ

end Langlands.Global.ArchimedeanGL
