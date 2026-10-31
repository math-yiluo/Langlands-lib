import Langlands.Global.ArchimedeanCompactTypes

/-! # Continuous projections onto actual archimedean compact types -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- An actual compact type has a continuous equivariant projection whose value
lies in the closed complex span of the compact orbit of its input. -/
def CompactTypeProjectionStatement : Prop :=
  ∀ σ : CompactType K n,
    ∃ P : DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n,
      (∀ f, P f ∈ compactTypeSubmodule σ) ∧
      (∀ f, f ∈ compactTypeSubmodule σ → P f = f) ∧
      (∀ (k : standardInfiniteCompact K n) f,
        P (compactAction K n k f) = compactAction K n k (P f)) ∧
      (∀ f, P f ∈
        (Submodule.span ℂ (Set.range fun k : standardInfiniteCompact K n =>
          compactAction K n k f)).topologicalClosure)

end Langlands.Global.ArchimedeanGL
