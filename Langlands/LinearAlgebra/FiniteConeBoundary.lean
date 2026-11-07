import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! # Supporting functionals for nonstrict finite conic combinations -/

noncomputable section

namespace Langlands.LinearAlgebra.FiniteConeBoundary

private theorem exists_functional_of_positive_image
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : (ι → ℝ) →ₗ[ℝ] E)
    (hF : Function.Surjective F) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hstrict : ¬ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧ F d = F c) :
    ∃ f : E →ₗ[ℝ] ℝ, f (F c) = 0 ∧
      (∀ i, 0 ≤ f (F (Pi.single i 1))) ∧
      ∃ i, 0 < f (F (Pi.single i 1)) := by
  classical
  let U : Set (ι → ℝ) := {d | ∀ i, 0 < d i}
  have hUopen : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hUconvex : Convex ℝ U := by
    intro x hx y hy a b ha hb hab i
    exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (hx i) (hy i) ha hb hab
  have hx : F c ∉ F '' U := by
    rintro ⟨d, hd, he⟩
    exact hstrict ⟨d, hd, he⟩
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open
    (hUconvex.linear_image F) (F.isOpenMap_of_finiteDimensional hF U hUopen) hx
  let o : ι → ℝ := fun _ => 1
  have hone : o ∈ U := fun _ => zero_lt_one
  have hnonneg : ∀ i, 0 ≤ f (F (Pi.single i 1)) := by
    intro i
    by_contra hi
    have hi' : f (F (Pi.single i 1)) < 0 := lt_of_not_ge hi
    let t : ℝ := (|f (F c)| + |f (F o)| + 1) / -f (F (Pi.single i 1))
    have ht : 0 ≤ t := div_nonneg (by positivity) (by linarith)
    have hmem : o + t • Pi.single i (1 : ℝ) ∈ U := by
      intro j
      change 0 < 1 + t * (Pi.single i (1 : ℝ) : ι → ℝ) j
      by_cases hji : j = i
      · subst j
        simpa using (show 0 < 1 + t from by linarith)
      · simp [hji]
    have h := hf _ ⟨_, hmem, rfl⟩
    simp only [map_add, map_smul, smul_eq_mul] at h
    have hmul : t * f (F (Pi.single i 1)) =
        -(|f (F c)| + |f (F o)| + 1) := by
      dsimp [t]
      field_simp [ne_of_lt hi']
    linarith [neg_abs_le (f (F c)), le_abs_self (f (F o))]
  have hcF : F c = ∑ i, c i • F (Pi.single i 1) := by
    simp_rw [← map_smul]
    rw [← map_sum]
    congr 1
    ext i
    simp [Pi.single_apply]
  have hcx : 0 ≤ f (F c) := by
    rw [hcF, map_sum]
    exact Finset.sum_nonneg fun i _ => by
      simpa only [map_smul, smul_eq_mul] using mul_nonneg (hc i) (hnonneg i)
  have hcx0 : f (F c) = 0 := by
    apply le_antisymm _ hcx
    by_contra hxpos
    have hxpos' : 0 < f (F c) := lt_of_not_ge hxpos
    have honepos : 0 < f (F o) := lt_trans hxpos' (hf _ ⟨_, hone, rfl⟩)
    let t : ℝ := f (F c) / (2 * f (F o))
    have ht : 0 < t := div_pos hxpos' (by positivity)
    have h := hf _ ⟨t • o, (fun _ => by simpa [o] using ht), rfl⟩
    simp only [map_smul, smul_eq_mul] at h
    have hmul : t * f (F o) = f (F c) / 2 := by
      dsimp [t]
      field_simp [ne_of_gt honepos]
    linarith
  refine ⟨f.toLinearMap, hcx0, hnonneg, ?_⟩
  by_contra hnone
  push Not at hnone
  have hz : ∀ i, f (F (Pi.single i 1)) = 0 :=
    fun i => le_antisymm (hnone i) (hnonneg i)
  have hoF : F o = ∑ i, F (Pi.single i 1) := by
    rw [← map_sum]
    congr 1
    ext i
    simp [o, Pi.single_apply]
  have h := hf _ ⟨_, hone, rfl⟩
  rw [hoF, map_sum, Finset.sum_eq_zero (fun i _ => hz i), hcx0] at h
  exact lt_irrefl _ h

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- A finite nonnegative combination which has no expansion with all coefficients
positive lies in the zero face of a functional nonnegative on every generator
and positive on at least one generator. Repetitions and linear dependence are allowed. -/
theorem exists_supporting_functional (v : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hstrict : ¬ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
      (∑ i, d i • v i) = ∑ i, c i • v i) :
    ∃ f : E →ₗ[ℝ] ℝ, f (∑ i, c i • v i) = 0 ∧
      (∀ i, 0 ≤ f (v i)) ∧ ∃ i, 0 < f (v i) := by
  classical
  let F := Fintype.linearCombination ℝ v
  let e := (Module.finBasis ℝ F.range).equivFun
  let F' := e.toLinearMap.comp F.rangeRestrict
  have hF' : Function.Surjective F' :=
    e.surjective.comp F.surjective_rangeRestrict
  have hstrict' : ¬ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧ F' d = F' c := by
    rintro ⟨d, hd, he⟩
    apply hstrict
    refine ⟨d, hd, ?_⟩
    have he' := e.injective he
    exact congrArg Subtype.val he'
  obtain ⟨f, hzero, hnonneg, hpos⟩ :=
    exists_functional_of_positive_image F' hF' c hc hstrict'
  let g := Subspace.dualLift F.range (f.comp e.toLinearMap)
  have hg : ∀ d, g (F d) = f (F' d) :=
    fun d => Subspace.dualLift_of_subtype (F.rangeRestrict d)
  have hv : ∀ i, F (Pi.single i 1) = v i := by
    intro i
    simp [F, Fintype.linearCombination_apply, Pi.single_apply]
  refine ⟨g, hg c |>.trans hzero, ?_, ?_⟩
  · intro i
    rw [← hv i, hg]
    exact hnonneg i
  · obtain ⟨i, hi⟩ := hpos
    exact ⟨i, by rwa [← hg, hv] at hi⟩

/-- A chosen actual supporting functional for the finite combination. -/
def supportingFunctional (v : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hstrict : ¬ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
      (∑ i, d i • v i) = ∑ i, c i • v i) : E →ₗ[ℝ] ℝ :=
  (exists_supporting_functional v c hc hstrict).choose

theorem supportingFunctional_spec (v : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hstrict : ¬ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
      (∑ i, d i • v i) = ∑ i, c i • v i) :
    supportingFunctional v c hc hstrict (∑ i, c i • v i) = 0 ∧
      (∀ i, 0 ≤ supportingFunctional v c hc hstrict (v i)) ∧
      ∃ i, 0 < supportingFunctional v c hc hstrict (v i) :=
  (exists_supporting_functional v c hc hstrict).choose_spec

end Langlands.LinearAlgebra.FiniteConeBoundary
