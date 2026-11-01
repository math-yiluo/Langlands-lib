import Langlands.Analysis.ProjectionClosureTransfer
import Langlands.Global.ArchimedeanCompactTypeProjectionProof
import Langlands.Representation.FiniteVectors

/-! # Closure transfer for actual compact types -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Orbit-closure-valued operators preserve compact-invariant submodules
consisting of actual compact-finite vectors. -/
theorem compactOrbitClosure_operator_preserves
    (M : Submodule ℂ (DerivativeSmoothFunctions K n))
    (h_invariant : ∀ (k : standardInfiniteCompact K n) f,
      f ∈ M → compactAction K n k f ∈ M)
    (h_finite : ∀ f, f ∈ M →
      Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (P : DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n)
    (h_orbit : ∀ f, P f ∈
      (Submodule.span ℂ (Set.range fun k : standardInfiniteCompact K n =>
        compactAction K n k f)).topologicalClosure) :
    ∀ f, f ∈ M → P f ∈ M := by
  intro f hf
  let O := Langlands.FiniteVectors.orbitSpan (compactAction K n) f
  have : Module.Finite ℂ O := h_finite f hf
  have h_le : O ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact h_invariant k f hf
  have h_closed : IsClosed (O : Set (DerivativeSmoothFunctions K n)) :=
    O.closed_of_finiteDimensional
  have hPf : P f ∈ O.topologicalClosure := h_orbit f
  rw [h_closed.submodule_topologicalClosure_eq] at hPf
  exact h_le hPf

/-- Finite compact-type intersections in a compact-finite invariant module
are unchanged by taking its closure. -/
theorem compactType_inf_topologicalClosure_eq
    (M : Submodule ℂ (DerivativeSmoothFunctions K n))
    (h_invariant : ∀ (k : standardInfiniteCompact K n) f,
      f ∈ M → compactAction K n k f ∈ M)
    (h_finite : ∀ f, f ∈ M →
      Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (σ : CompactType K n)
    [Module.Finite ℂ (M ⊓ compactTypeSubmodule σ :
      Submodule ℂ (DerivativeSmoothFunctions K n))] :
    M.topologicalClosure ⊓ compactTypeSubmodule σ =
      M ⊓ compactTypeSubmodule σ := by
  obtain ⟨P, h_range, h_fix, _h_equivariant, h_orbit⟩ := compactTypeProjection K n σ
  exact Langlands.Analysis.inf_topologicalClosure_eq_of_projection
    M (compactTypeSubmodule σ) P h_range h_fix
    (compactOrbitClosure_operator_preserves K n M h_invariant h_finite P h_orbit)

end Langlands.Global.ArchimedeanGL
