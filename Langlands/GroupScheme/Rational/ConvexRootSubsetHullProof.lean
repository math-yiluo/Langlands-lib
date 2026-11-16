import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.Geometry.FiniteConeClosed

/-! # The finite-hull characterization of convex relative-root subsets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

/-- Renard V.4.2: a subset of either relative-root ambient set is convex exactly
when it contains every ambient root in its conic hull. -/
theorem convexRootSubsetHull : ConvexRootSubsetHullStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hG.smooth
  intro R hR X
  have hfin : R.Finite := by
    have hroots := hi.isSplitSubtorus.1.finite_relativeRoots i
    rcases hR with rfl | rfl
    · exact hroots
    · exact hroots.subset fun _ h => h.1
  constructor
  · rintro ⟨C, -, hXC⟩
    have hXin : ∀ χ ∈ X, (1 : ℝ) ⊗ₜ[ℤ] χ ∈ C := by
      intro χ hχ
      rw [hXC] at hχ
      exact hχ.2
    refine ⟨?_, ?_⟩
    · intro χ hχ
      rw [hXC] at hχ
      exact hχ.1
    · intro γ hγ hHull
      rw [hXC]
      refine ⟨hγ, ?_⟩
      have hle : PointedCone.hull ℝ ((fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ) '' X) ≤ C := by
        apply Submodule.span_le.mpr
        rintro _ ⟨χ, hχ, rfl⟩
        exact hXin χ hχ
      exact hle hHull
  · rintro ⟨hXR, hHull⟩
    refine ⟨PointedCone.hull ℝ ((fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ) '' X), ?_, ?_⟩
    · exact Langlands.Geometry.FiniteCone.isClosed_hull_moduleTopology
        ((hfin.subset hXR).image fun χ => (1 : ℝ) ⊗ₜ[ℤ] χ)
    · ext γ
      constructor
      · intro hγ
        exact ⟨hXR hγ, PointedCone.subset_hull ⟨γ, hγ, rfl⟩⟩
      · intro hγ
        exact hHull γ hγ.1 hγ.2

end Langlands.GroupScheme
