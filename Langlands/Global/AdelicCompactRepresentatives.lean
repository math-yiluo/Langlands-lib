import Langlands.Global.AdeleQuotientCompactProof

/-! # Compact representatives for the actual additive adele quotient -/

noncomputable section

universe u

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- The standard compact fundamental set meets every additive diagonal coset. -/
theorem exists_compact_sub_diagonal_mem :
    ∃ C : Set (Adeles K), IsCompact C ∧
      ∀ a : Adeles K, ∃ x : K, a - diagonal K x ∈ C := by
  refine ⟨archimedeanFundamentalSet K ×ˢ
    (integralFiniteAdeles K : Set (FiniteAdeles K)),
    (isCompact_archimedeanFundamentalSet K).prod (isCompact_integralFiniteAdeles K), ?_⟩
  intro a
  obtain ⟨x, hx⟩ := exists_sub_mem_integralFiniteAdeles a.2
  obtain ⟨y, hy⟩ := exists_sub_integer_mem_archimedeanFundamentalSet K
    (a.1 - algebraMap K (InfiniteAdeles K) x)
  have hyf : algebraMap K (FiniteAdeles K) (y : K) ∈ integralFiniteAdeles K :=
    (mem_integralFiniteAdeles K _).mpr fun v ↦
      IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v y
  refine ⟨x + (y : K), ?_, ?_⟩
  · change a.1 - algebraMap K (InfiniteAdeles K) (x + (y : K)) ∈ _
    rwa [map_add, ← sub_sub]
  · change a.2 - algebraMap K (FiniteAdeles K) (x + (y : K)) ∈ integralFiniteAdeles K
    rw [map_add, ← sub_sub]
    exact (integralFiniteAdeles K).sub_mem hx hyf

end Langlands.Global
