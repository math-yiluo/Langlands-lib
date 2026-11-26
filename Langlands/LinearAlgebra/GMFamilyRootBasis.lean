import Langlands.LinearAlgebra.GMFamilies
import Mathlib.Algebra.Group.Irreducible.Indecomposable
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.Tactic

/-! # Simple roots of the Euclidean arrangement -/

noncomputable section

open scoped RealInnerProductSpace
open Submodule
open Classical

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {R : Finset E}

/-- The indecomposable roots among the roots positive at `h`. -/
def positiveSimpleRoots (R : Finset E) (h : E) : Finset E :=
  (posSet R h).filter fun v => ¬ ∃ u ∈ posSet R h, ∃ w ∈ posSet R h, v = u + w

theorem mem_posSet_iff {x h : E} : x ∈ posSet R h ↔ x ∈ R ∧ 0 < ⟪x, h⟫ :=
  Finset.mem_filter

theorem neg_mem_rootSet (hR : IsRootSet R) {x : E} (hx : x ∈ R) : -x ∈ R := by
  have hn : x ≠ 0 := fun he => hR.1 (he ▸ hx)
  have hd : ⟪x, x⟫ ≠ 0 := by simpa using hn
  convert hR.2.1 x hx x hx using 1
  rw [mul_div_cancel_right₀ _ hd, two_smul]
  abel

theorem neg_mem_rootSet_iff (hR : IsRootSet R) {x : E} : -x ∈ R ↔ x ∈ R := by
  refine ⟨fun hx => ?_, neg_mem_rootSet hR⟩
  simpa using neg_mem_rootSet hR hx

private theorem root_sub_mem_of_inner_pos (hR : IsRootSet R) {x y : E}
    (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y) (hp : 0 < ⟪x, y⟫) : x - y ∈ R := by
  have hx0 : x ≠ 0 := fun he => hR.1 (he ▸ hx)
  have hy0 : y ≠ 0 := fun he => hR.1 (he ▸ hy)
  have hxx : 0 < ⟪x, x⟫ := real_inner_self_pos.mpr hx0
  have hyy : 0 < ⟪y, y⟫ := real_inner_self_pos.mpr hy0
  obtain ⟨m, hm⟩ := hR.2.2 x hx y hy
  obtain ⟨n, hn⟩ := hR.2.2 y hy x hx
  rw [real_inner_comm x y] at hm
  have hm0 : 0 < m := by
    exact_mod_cast (hm ▸ div_pos (mul_pos (by norm_num) hp) hxx : 0 < (m : ℝ))
  have hn0 : 0 < n := by
    exact_mod_cast (hn ▸ div_pos (mul_pos (by norm_num) hp) hyy : 0 < (n : ℝ))
  by_cases hm1 : m = 1
  · have href := hR.2.1 x hx y hy
    rw [real_inner_comm x y, hm, hm1, Int.cast_one, one_smul] at href
    simpa using neg_mem_rootSet hR href
  by_cases hn1 : n = 1
  · have href := hR.2.1 y hy x hx
    rwa [hn, hn1, Int.cast_one, one_smul] at href
  have hmn : m * n ≤ 4 := by
    have hbound := real_inner_mul_inner_self_le x y
    have hreal : (m : ℝ) * (n : ℝ) ≤ 4 := by
      rw [← hm, ← hn, div_mul_div_comm, div_le_iff₀ (mul_pos hxx hyy)]
      nlinarith only [hbound]
    exact_mod_cast hreal
  have hmge : 2 ≤ m := by omega
  have hnge : 2 ≤ n := by omega
  have hmle := (mul_le_mul_of_nonneg_left hnge hm0.le).trans hmn
  have hnle := (mul_le_mul_of_nonneg_right hmge hn0.le).trans hmn
  have hm2 : m = 2 := by omega
  have hn2 : n = 2 := by omega
  rw [hm2, Int.cast_ofNat, div_eq_iff hxx.ne'] at hm
  rw [hn2, Int.cast_ofNat, div_eq_iff hyy.ne'] at hn
  have hzero : ⟪x - y, x - y⟫ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm x y]
    linarith
  exact False.elim (hxy (sub_eq_zero.mp (inner_self_eq_zero.mp hzero)))

/-- Every positive root is a nonnegative integral combination of the simple roots. -/
theorem root_mem_closure_positiveSimpleRoots {h x : E} (hx : x ∈ posSet R h) :
    x ∈ AddSubmonoid.closure (↑(positiveSimpleRoots R h) : Set E) := by
  let v : R → E := Subtype.val
  let f : E →+ ℝ := ((innerₗ E h).toAddHom)
  have hset : v '' IsAddIndecomposable.baseOf v f = ↑(positiveSimpleRoots R h) := by
    ext y
    simp only [Set.mem_image, IsAddIndecomposable.baseOf, Set.mem_ofPred_eq,
      IsAddIndecomposable, positiveSimpleRoots, Finset.mem_coe, Finset.mem_filter,
      mem_posSet_iff]
    have heval (i : R) : f (v i) = ⟪(i : E), h⟫ := real_inner_comm _ _
    simp only [heval]
    constructor
    · rintro ⟨i, ⟨hi, hind⟩, rfl⟩
      refine ⟨⟨i.prop, hi⟩, fun ⟨u, hu, w, hw, he⟩ => ?_⟩
      rcases hind ⟨u, hu.1⟩ hu.2 ⟨w, hw.1⟩ hw.2 he with hu0 | hw0
      · change u = 0 at hu0
        simpa [hu0] using hu.2
      · change w = 0 at hw0
        simpa [hw0] using hw.2
    · rintro ⟨⟨hy, hp⟩, hind⟩
      exact ⟨⟨y, hy⟩, ⟨hp, fun i hi j hj he => (hind ⟨i, ⟨i.prop, hi⟩,
        j, ⟨j.prop, hj⟩, he⟩).elim⟩, rfl⟩
  rw [← hset, AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
  exact AddSubmonoid.subset_closure ⟨⟨x, (mem_posSet_iff.mp hx).1⟩,
    by simpa [f, v, real_inner_comm h] using (mem_posSet_iff.mp hx).2, rfl⟩

/-- The simple roots are independent when the reference point is regular on the root span. -/
theorem linearIndependent_positiveSimpleRoots (hR : IsRootSet R) {h : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) :
    LinearIndependent ℝ (fun x : positiveSimpleRoots R h => (x : E)) := by
  have hpos : (LinearMap.BilinMap.toQuadraticMap (innerₗ E)).PosDef :=
    fun _ hx => real_inner_self_pos.mpr hx
  refine LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero (innerₗ E) hpos
    (innerₗ E h) _ ?_ ?_
  · intro i
    rw [innerₗ_apply_apply, real_inner_comm]
    exact (mem_posSet_iff.mp (Finset.mem_filter.mp i.prop).1).2
  · intro i j hij
    change ⟪(i : E), (j : E)⟫ ≤ 0
    by_contra! hp
    have hi := Finset.mem_filter.mp i.prop
    have hj := Finset.mem_filter.mp j.prop
    have hd := root_sub_mem_of_inner_pos hR (mem_posSet_iff.mp hi.1).1
      (mem_posSet_iff.mp hj.1).1 (fun he => hij (Subtype.ext he)) hp
    rcases lt_or_gt_of_ne (hh _ hd) with hn | hn
    · have hj' : (j : E) - i ∈ posSet R h := by
        refine mem_posSet_iff.mpr ⟨?_, ?_⟩
        · simpa only [neg_sub] using neg_mem_rootSet hR hd
        · rw [inner_sub_left] at hn ⊢
          linarith
      exact hj.2 ⟨i, hi.1, (j : E) - i, hj', by abel⟩
    · have hi' : (i : E) - j ∈ posSet R h := mem_posSet_iff.mpr ⟨hd, hn⟩
      exact hi.2 ⟨j, hj.1, (i : E) - j, hi', by abel⟩

/-- The simple roots span the full root space. -/
theorem span_positiveSimpleRoots (hR : IsRootSet R) {h : E}
    (hh : ∀ x ∈ R, ⟪x, h⟫ ≠ 0) :
    span ℝ (↑(positiveSimpleRoots R h) : Set E) = span ℝ (↑R : Set E) := by
  apply le_antisymm
  · exact span_mono fun x hx => (mem_posSet_iff.mp (Finset.mem_filter.mp hx).1).1
  have hpos (x : E) (hx : x ∈ posSet R h) :
      x ∈ span ℝ (↑(positiveSimpleRoots R h) : Set E) :=
    AddSubmonoid.closure_le.mpr (fun _ hy => subset_span hy)
      (root_mem_closure_positiveSimpleRoots hx)
  refine span_le.mpr (fun x hx => ?_)
  rcases lt_or_gt_of_ne (hh x hx) with hneg | hpos'
  · apply (Submodule.neg_mem_iff _).mp
    exact hpos _ (mem_posSet_iff.mpr ⟨neg_mem_rootSet hR hx, by simpa using hneg⟩)
  · exact hpos x (mem_posSet_iff.mpr ⟨hx, hpos'⟩)

end Langlands.GMFamily
