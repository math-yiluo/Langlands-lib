import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Option

noncomputable section

open Filter Topology

namespace Langlands.Global.DivisorEulerProduct

universe u
variable {ι : Type u}

local instance divisorEulerProductDecidableEq : DecidableEq ι := Classical.decEq ι
local instance divisorEulerProductDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The coefficient retains the zeroth local coefficients at the exceptional places. -/
def coefficient (S : Finset ι) (h : ι → ℤ → ℂ) (d : ι →₀ ℤ) : ℂ :=
  ∏ i ∈ S ∪ d.support, h i (d i)

/-- The finite graph includes every exceptional coordinate, even when its value is zero. -/
def coefficientGraph (S : Finset ι) (d : ι →₀ ℤ) : Finset (ι × ℤ) :=
  (S ∪ d.support).map ⟨fun i => (i, d i), fun _ _ h => (Prod.mk.inj h).1⟩

@[simp] theorem mem_coefficientGraph (S : Finset ι) (d : ι →₀ ℤ) (i : ι) (k : ℤ) :
    (i, k) ∈ coefficientGraph S d ↔ (i ∈ S ∨ d i ≠ 0) ∧ d i = k := by
  classical
  simp only [coefficientGraph, Finset.mem_map, Finset.mem_union, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩
    exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem coefficientGraph_injective (S : Finset ι) :
    Function.Injective (coefficientGraph S : (ι →₀ ℤ) → Finset (ι × ℤ)) := by
  intro d e h
  ext i
  by_cases hd : d i = 0
  · by_cases he : e i = 0
    · exact hd.trans he.symm
    · have hm : (i, e i) ∈ coefficientGraph S e :=
        (mem_coefficientGraph S e i (e i)).mpr ⟨Or.inr he, rfl⟩
      rw [← h] at hm
      exact (mem_coefficientGraph S d i (e i)).mp hm |>.2
  · have hm : (i, d i) ∈ coefficientGraph S d :=
      (mem_coefficientGraph S d i (d i)).mpr ⟨Or.inr hd, rfl⟩
    rw [h] at hm
    exact ((mem_coefficientGraph S e i (d i)).mp hm).2.symm

/-- Only finitely many zero-index weights are retained. -/
def graphWeight (S : Finset ι) (h : ι → ℤ → ℂ) (p : ι × ℤ) : ℂ :=
  if p.1 ∈ S ∨ p.2 ≠ 0 then h p.1 p.2 else 0

theorem prod_graphWeight (S : Finset ι) (h : ι → ℤ → ℂ) (d : ι →₀ ℤ) :
    (∏ p ∈ coefficientGraph S d, graphWeight S h p) = coefficient S h d := by
  classical
  rw [coefficientGraph, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i hi
  change (if i ∈ S ∨ d i ≠ 0 then h i (d i) else 0) = h i (d i)
  exact ite_eq_left (by simpa only [Finset.mem_union, Finsupp.mem_support_iff] using hi)

theorem summable_norm_graphWeight (S : Finset ι) (h : ι → ℤ → ℂ)
    (hh : Summable (fun p : ι × ℤ => if p.2 = 0 then (0 : ℝ) else ‖h p.1 p.2‖)) :
    Summable (fun p => ‖graphWeight S h p‖) := by
  classical
  have hz : Summable (fun p : ι × ℤ =>
      if p.1 ∈ S ∧ p.2 = 0 then ‖h p.1 p.2‖ else 0) := by
    apply summable_of_ne_finset_zero (s := S ×ˢ {0})
    intro p hp
    exact ite_eq_right (by
      simpa only [Finset.mem_product, Finset.mem_singleton] using hp)
  convert hz.add hh using 1
  funext p
  by_cases hk : p.2 = 0 <;> by_cases hi : p.1 ∈ S <;>
    simp [graphWeight, hk, hi]

/-- Absolute convergence of the divisor series, including arbitrary exceptional zero terms. -/
theorem summable_norm_coefficient (S : Finset ι) (h : ι → ℤ → ℂ)
    (hh : Summable (fun p : ι × ℤ => if p.2 = 0 then (0 : ℝ) else ‖h p.1 p.2‖)) :
    Summable (fun d : ι →₀ ℤ => ‖coefficient S h d‖) := by
  have hg := summable_norm_graphWeight S h hh
  have hf := (summable_finsetProd_of_summable_nonneg
    (fun p => norm_nonneg (graphWeight S h p)) hg).comp_injective
      (coefficientGraph_injective S)
  refine hf.congr fun d => ?_
  rw [← prod_graphWeight, norm_prod]
  rfl

/-- A finite family of absolutely convergent local series can be multiplied. -/
theorem finite_series_product {α : Type u} [Fintype α] (h : α → ℤ → ℂ)
    (hh : ∀ i, Summable (fun k => ‖h i k‖)) :
    Summable (fun d : α → ℤ => ‖∏ i, h i (d i)‖) ∧
      (∑' d : α → ℤ, ∏ i, h i (d i)) = ∏ i, ∑' k, h i k := by
  classical
  let P := fun (α : Type u) [Fintype α] =>
    ∀ h : α → ℤ → ℂ, (∀ i, Summable (fun k => ‖h i k‖)) →
      Summable (fun d : α → ℤ => ‖∏ i, h i (d i)‖) ∧
        (∑' d : α → ℤ, ∏ i, h i (d i)) = ∏ i, ∑' k, h i k
  apply Fintype.induction_empty_option (P := P) ?_ ?_ ?_ α h hh
  · intro α β _ e ih h hh
    let : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨hs, he⟩ := ih (fun i => h (e i)) (fun i => hh (e i))
    let E : (α → ℤ) ≃ (β → ℤ) := e.arrowCongr (Equiv.refl ℤ)
    have key (d : α → ℤ) :
        (∏ i, h i (E d i)) = ∏ i, h (e i) (d i) := by
      rw [← e.prod_comp]
      simp [E, Equiv.arrowCongr]
    constructor
    · rw [← E.summable_iff]
      exact hs.congr fun d => by simp only [Function.comp_apply, key]
    · rw [← E.tsum_eq (fun d => ∏ i, h i (d i))]
      simp_rw [key]
      exact he.trans (e.prod_comp (fun i => ∑' k, h i k))
  · intro h hh
    constructor
    · exact Summable.of_finite
    · simp
  · intro α _ ih h hh
    obtain ⟨hs, he⟩ := ih (fun i => h (some i)) (fun i => hh (some i))
    let E : (Option α → ℤ) ≃ (ℤ × (α → ℤ)) := Equiv.piOptionEquivProd
    have key (d : Option α → ℤ) :
        (∏ i, h i (d i)) = h none (E d).1 * ∏ i, h (some i) ((E d).2 i) := by
      exact Fintype.prod_option _
    constructor
    · have hp := (hh none).mul_norm hs
      exact (hp.comp_injective E.injective).congr fun d => by
        simp only [Function.comp_apply, ← key]
    · calc
        (∑' d : Option α → ℤ, ∏ i, h i (d i)) =
            ∑' p : ℤ × (α → ℤ), h none p.1 * ∏ i, h (some i) (p.2 i) := by
          rw [← E.tsum_eq]
          apply tsum_congr key
        _ = (∑' k, h none k) * (∑' d : α → ℤ, ∏ i, h (some i) (d i)) :=
          (tsum_mul_tsum_of_summable_norm (hh none) hs).symm
        _ = ∏ i, ∑' k, h i k := by rw [he, Fintype.prod_option]

/-- Restricting the support of a divisor to a finite set gives a finite tuple of integers. -/
def supportEquiv (T : Finset ι) :
    {d : ι →₀ ℤ // (↑d.support : Set ι) ⊆ (T : Set ι)} ≃ (T → ℤ) :=
  (Finsupp.restrictSupportEquiv (T : Set ι) ℤ).trans Finsupp.equivFunOnFinite

@[simp] theorem supportEquiv_apply (T : Finset ι)
    (d : {d : ι →₀ ℤ // (↑d.support : Set ι) ⊆ (T : Set ι)}) (i : T) :
    supportEquiv T d i = d.1 i := rfl

theorem coefficient_eq_prod (S T : Finset ι) (h : ι → ℤ → ℂ)
    (hzero : ∀ i ∉ S, h i 0 = 1) (hST : S ⊆ T)
    (d : {d : ι →₀ ℤ // (↑d.support : Set ι) ⊆ (T : Set ι)}) :
    coefficient S h d.1 = ∏ i : T, h i (supportEquiv T d i) := by
  classical
  simp only [supportEquiv_apply, coefficient]
  change _ = ∏ i : T, (fun j : ι => h j (d.1 j)) i
  rw [Finset.prod_coe_sort T (fun j : ι => h j (d.1 j))]
  apply Finset.prod_subset (Finset.union_subset hST d.2)
  intro i _ hi
  have hnot : i ∉ S ∧ i ∉ d.1.support := by
    simpa only [Finset.mem_union, not_or] using hi
  rw [Finsupp.notMem_support_iff.mp hnot.2]
  exact hzero i hnot.1

/-- The sum of coefficients whose support lies in `T` is the corresponding local product. -/
theorem sum_restrict_support (S T : Finset ι) (h : ι → ℤ → ℂ)
    (hzero : ∀ i ∉ S, h i 0 = 1) (hST : S ⊆ T)
    (hh : ∀ i, Summable (fun k => ‖h i k‖)) :
    (∑' d : ι →₀ ℤ, if (↑d.support : Set ι) ⊆ (T : Set ι)
      then coefficient S h d else 0) = ∏ i ∈ T, ∑' k, h i k := by
  classical
  change (∑' d, {d : ι →₀ ℤ | (↑d.support : Set ι) ⊆ (T : Set ι)}.indicator
    (coefficient S h) d) = _
  rw [← tsum_subtype]
  calc
    _ = ∑' d : {d : ι →₀ ℤ // (↑d.support : Set ι) ⊆ (T : Set ι)},
        ∏ i : T, h i (supportEquiv T d i) :=
      tsum_congr (fun d => coefficient_eq_prod S T h hzero hST d)
    _ = ∑' d : T → ℤ, ∏ i : T, h i (d i) :=
      (supportEquiv T).tsum_eq (fun d : T → ℤ => ∏ i : T, h i (d i))
    _ = ∏ i ∈ T, ∑' k, h i k :=
      (finite_series_product (fun i : T => h i) (fun i => hh i)).2.trans
        (Finset.prod_coe_sort T (fun i => ∑' k, h i k))

/-- The absolutely convergent divisor series equals the unordered product of local series. -/
theorem hasProd_tsum (S : Finset ι) (h : ι → ℤ → ℂ)
    (hzero : ∀ i ∉ S, h i 0 = 1)
    (hh : Summable (fun p : ι × ℤ => if p.2 = 0 then (0 : ℝ) else ‖h p.1 p.2‖)) :
    HasProd (fun i => ∑' k, h i k) (∑' d : ι →₀ ℤ, coefficient S h d) := by
  classical
  have hlocal (i : ι) : Summable (fun k => ‖h i k‖) := by
    have hs := hh.comp_injective (fun _ _ h => (Prod.mk.inj h).2 :
      Function.Injective (fun k : ℤ => (i, k)))
    apply hs.congr_cofinite
    filter_upwards [eventually_cofinite_ne (0 : ℤ)] with k hk
    simp only [Function.comp_apply, ite_eq_right hk]
  have hlim := tendsto_tsum_of_dominated_convergence (summable_norm_coefficient S h hh)
    (f := fun T : Finset ι => fun d : ι →₀ ℤ =>
      if (↑d.support : Set ι) ⊆ (T : Set ι) then coefficient S h d else 0)
    (g := coefficient S h) (𝓕 := atTop)
    (fun d => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop d.support] with T hT
      exact (ite_eq_left hT).symm)
    (Filter.Eventually.of_forall (fun T d => by split_ifs <;> simp))
  change Tendsto (fun T : Finset ι => ∏ i ∈ T, ∑' k, h i k) atTop
    (𝓝 (∑' d : ι →₀ ℤ, coefficient S h d))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop S] with T hT
  exact sum_restrict_support S T h hzero hT hlocal

end Langlands.Global.DivisorEulerProduct
