import Langlands.Representation.Hecke.FixedVectorCornerStatements
import Mathlib.LinearAlgebra.Projection

/-! # Kernel and complement of the compact-open fixed-vector projection -/

namespace Langlands.Hecke

open MeasureTheory

universe u v

/-- Renard III.1.5, Proposition (ii)–(iii), for the published projection. -/
theorem fixedProjectionKernel : FixedProjectionKernelStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ A K hK
  let P := fixedProjection μ A.representation A.isSmooth K hK
  refine ⟨le_antisymm ?_ ?_, LinearMap.isCompl_of_proj
    (fixedProjection_fixed μ A.representation A.isSmooth K hK)⟩
  · intro x hx
    have hx0 : P x = 0 := hx
    have hmem : (P (-x) : A) - (-x) ∈
        Submodule.span ℂ (Set.range fun x : A => (P x : A) - x) :=
      Submodule.subset_span ⟨-x, rfl⟩
    simpa only [map_neg, hx0, neg_zero, ZeroMemClass.coe_zero, zero_sub, neg_neg]
      using hmem
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    change P ((P x : A) - x) = 0
    rw [map_sub, fixedProjection_fixed, sub_self]

end Langlands.Hecke
