import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Normed.Field.Krasner

/-! # A coefficient neighborhood preserving a simple field extension -/

noncomputable section

namespace Langlands.Global.FieldRealization

open Polynomial IntermediateField

universe u v

variable {K : Type u} {L : Type v} [NormedField K] [NormedField L] [NormedAlgebra K L]

/-- A positive separation bound for the distinct conjugates of `x`. The extra `1`
handles the case in which `x` has no other conjugates. -/
def conjugateRadius (K : Type u) [NormedField K] [NormedAlgebra K L] (x : L) : ℝ := by
  classical
  exact (insert 1 (((minpoly K x).aroots L).toFinset.erase x |>.image fun y => ‖x - y‖)).inf'
    (by simp) id

theorem conjugateRadius_pos (x : L) : 0 < conjugateRadius K x := by
  classical
  unfold conjugateRadius
  rw [Finset.lt_inf'_iff]
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · norm_num
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_erase.mp hy).1.symm)

theorem conjugateRadius_le (x y : L) (hx : IsIntegral K x)
    (hy : IsConjRoot K x y) (hne : x ≠ y) : conjugateRadius K x ≤ ‖x - y‖ := by
  classical
  unfold conjugateRadius
  apply Finset.inf'_le id
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨y, Finset.mem_erase.mpr ⟨hne.symm, ?_⟩, rfl⟩
  simpa only [Multiset.mem_toFinset] using
    (isConjRoot_iff_mem_minpoly_aroots hx).mp hy

/-- An explicit coefficient radius making the quantitative root bound smaller
than the separation of the conjugates of `x`. -/
def coefficientRadius (K : Type u) [NormedField K] [NormedAlgebra K L] (x : L) : ℝ :=
  (conjugateRadius K x / max ‖x‖ 1) ^ (minpoly K x).natDegree /
    ((minpoly K x).natDegree + 1)

theorem coefficientRadius_pos (x : L) : 0 < coefficientRadius K x := by
  unfold coefficientRadius
  have h := conjugateRadius_pos (K := K) x
  positivity

theorem coefficientRadius_rootBound (x : L) (hx : IsIntegral K x) :
    (((minpoly K x).natDegree + 1) * coefficientRadius K x) ^
        ((minpoly K x).natDegree : ℝ)⁻¹ * max ‖x‖ 1 = conjugateRadius K x := by
  have hn : (minpoly K x).natDegree ≠ 0 := (minpoly.natDegree_pos hx).ne'
  have hA : 0 < max ‖x‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ : 0 ≤ conjugateRadius K x / max ‖x‖ 1 :=
    (div_pos (conjugateRadius_pos x) hA).le
  have hN : ((minpoly K x).natDegree : ℝ) + 1 ≠ 0 := by positivity
  unfold coefficientRadius
  rw [mul_div_cancel₀ _ hN, Real.pow_rpow_inv_natCast hδ hn, div_mul_cancel₀ _ hA.ne']

/-- Every sufficiently close monic polynomial of the same degree has a root
which generates exactly the same intermediate field. The ambient field must
contain the roots of both polynomials and satisfy Krasner's lemma. -/
theorem exists_root_adjoin_eq_of_coeff_lt [IsKrasner K L] (x : L)
    (hx : IsSeparable K x) (hf : ((minpoly K x).map (algebraMap K L)).Splits)
    (g : Polynomial K) (hgm : g.Monic) (hdeg : g.natDegree = (minpoly K x).natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - (minpoly K x).coeff i‖ < coefficientRadius K x)
    (hg : (g.map (algebraMap K L)).Splits) :
    ∃ y : L, aeval y g = 0 ∧ K⟮x⟯ = K⟮y⟯ := by
  obtain ⟨y, hy, hdist⟩ := Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
    (coefficientRadius_pos (K := K) x) (minpoly.aeval K x) (minpoly.monic hx.isIntegral)
    hgm hdeg hcoeff hg
  rw [coefficientRadius_rootBound x hx.isIntegral] at hdist
  have hy0 : aeval y g = 0 := (Polynomial.mem_aroots.mp hy).2
  have hyi : IsIntegral K y := ⟨g, hgm, hy0⟩
  have hxy : x ∈ K⟮y⟯ := IsKrasner.krasner hx hf hyi fun z hz hne =>
    hdist.trans_le (conjugateRadius_le x z hx.isIntegral hz hne)
  have := IntermediateField.adjoin.finiteDimensional hyi
  refine ⟨y, hy0, IntermediateField.eq_of_le_of_finrank_le
    (IntermediateField.adjoin_simple_le_iff.mpr hxy) ?_⟩
  rw [IntermediateField.adjoin.finrank hyi, IntermediateField.adjoin.finrank hx.isIntegral]
  exact (Polynomial.natDegree_le_natDegree (minpoly.min K y hgm hy0)).trans_eq hdeg

end Langlands.Global.FieldRealization
