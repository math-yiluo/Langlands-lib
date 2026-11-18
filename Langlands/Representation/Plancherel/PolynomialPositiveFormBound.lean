import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation
import Langlands.Representation.Unitary.HermitianDual
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Uniform functional bounds on polynomial operator ranges -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel.UnramifiedOperatorFamily

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {U : Set (unramifiedCharacters ν)} {f : U → W}

/-- The values of a polynomial vector family belong to one finite-dimensional
subspace, even when its ambient carrier has no chosen topology. -/
theorem exists_finiteSubmodule_of_isPolynomialOn (hf : IsPolynomialOn U f) :
    ∃ S : Submodule ℂ W, Module.Finite ℂ S ∧ ∀ z, f z ∈ S := by
  obtain ⟨n, a, w, hf⟩ := hf
  refine ⟨Submodule.span ℂ (Set.range w), Module.Finite.span_of_finite ℂ (Set.finite_range w), ?_⟩
  intro z
  rw [hf z]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- A chosen finite-dimensional range subspace for an actual polynomial family. -/
def polynomialRangeSubmodule (hf : IsPolynomialOn U f) : Submodule ℂ W :=
  Classical.choose (exists_finiteSubmodule_of_isPolynomialOn hf)

theorem polynomialRangeSubmodule_finite (hf : IsPolynomialOn U f) :
    Module.Finite ℂ (polynomialRangeSubmodule hf) :=
  (Classical.choose_spec (exists_finiteSubmodule_of_isPolynomialOn hf)).1

theorem mem_polynomialRangeSubmodule (hf : IsPolynomialOn U f) (z : U) :
    f z ∈ polynomialRangeSubmodule hf :=
  (Classical.choose_spec (exists_finiteSubmodule_of_isPolynomialOn hf)).2 z

section Bound

omit [Group G] [TopologicalSpace G] in
/-- Every functional is bounded in the norm of an algebraic positive inner
product when restricted to a finite-dimensional subspace. -/
theorem exists_functional_sq_bound_on_finiteSubmodule
    (c : InnerProductSpace.Core ℂ W) (S : Submodule ℂ W) [Module.Finite ℂ S]
    (ℓ : W →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ S, ‖ℓ w‖ ^ 2 ≤ C * (c.inner w w).re := by
  let _ : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ W _ _ _ c
  let _ : InnerProductSpace ℂ W := InnerProductSpace.ofCore c.toCore
  let T : S →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (ℓ.comp S.subtype)
  let C := max 1 ‖T‖
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C ^ 2, sq_pos_of_pos hC, fun w hw => ?_⟩
  let x : S := ⟨w, hw⟩
  have hb : ‖ℓ w‖ ≤ C * ‖x‖ :=
    (T.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_right 1 ‖T‖) (norm_nonneg x))
  have hs := pow_le_pow_left₀ (norm_nonneg (ℓ w)) hb 2
  have hnx : ‖x‖ ^ 2 = (c.inner w w).re := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x
  rwa [mul_pow, hnx] at hs

end Bound

variable {Ω : Set (unramifiedCharacters ν)} {A : Ω → V →ₗ[ℂ] W}

/-- Every regular value of a continued operator on one input lies in the
finite-dimensional range space of its polynomial numerator. -/
theorem continuedOperator_mem_polynomialRangeSubmodule
    (p : RationalOperatorContinuationData Ω A) (v : V) (z : p.regularRegion) :
    p.continuedOperator z v ∈ polynomialRangeSubmodule (p.polynomial v) := by
  apply Submodule.smul_mem
  exact mem_polynomialRangeSubmodule (p.polynomial v) ⟨z.val, Set.mem_univ _⟩

/-- A single constant bounds a functional on every regular value of the
continued operator in terms of its positive quadratic form. No parameter
compactness or topology on the ambient representation is assumed. -/
theorem exists_continuedOperator_functional_sq_bound
    (p : RationalOperatorContinuationData Ω A) (v : V)
    (c : InnerProductSpace.Core ℂ W) (ℓ : W →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : p.regularRegion,
      ‖ℓ (p.continuedOperator z v)‖ ^ 2 ≤
        C * (c.inner (p.continuedOperator z v) (p.continuedOperator z v)).re := by
  have := polynomialRangeSubmodule_finite (p.polynomial v)
  obtain ⟨C, hC, hbound⟩ := exists_functional_sq_bound_on_finiteSubmodule c
    (polynomialRangeSubmodule (p.polynomial v)) ℓ
  exact ⟨C, hC, fun z => hbound _ (continuedOperator_mem_polynomialRangeSubmodule p v z)⟩

end Langlands.Plancherel.UnramifiedOperatorFamily
