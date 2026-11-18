import Langlands.GroupScheme.Composition.CayleyGrading

/-! # Gradings of a Cayley datum from weighted self-dual frames -/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.CayleyDatum

variable {K : Type u} [Field K] (c : CayleyDatum K)

local notation "μ" => c.multiplication

/-- A weighted self-dual frame of a Cayley datum: eight vectors `vec i`, an involution `dual`
such that `vec i` pairs to one with `vec (dual i)` and to zero with every other frame vector,
and weights with `weight (dual i) = -weight i`, such that the unit only pairs with frame
vectors of weight zero and `b(vec i * vec j, vec l)` vanishes unless the three weights
sum to zero. -/
structure WeightedFrame (ι : Type w) [Fintype ι] [DecidableEq ι] (M : Type v)
    [AddCommGroup M] where
  /-- The frame vectors. -/
  vec : ι → CayleyVector K
  /-- The index of the dual frame vector. -/
  dual : ι → ι
  /-- The weight of a frame vector. -/
  weight : ι → M
  dual_dual : ∀ i, dual (dual i) = i
  card_eq : Fintype.card ι = 8
  form_vec : ∀ i j, c.form (vec i) (vec j) = if j = dual i then 1 else 0
  weight_dual : ∀ i, weight (dual i) = -weight i
  form_unit : ∀ i, weight i ≠ 0 → c.form c.unit (vec i) = 0
  form_mul : ∀ i j l, weight i + weight j + weight l ≠ 0 →
    c.form (μ (vec i) (vec j)) (vec l) = 0

namespace WeightedFrame

variable {c} {ι : Type w} [Fintype ι] [DecidableEq ι] {M : Type v} [AddCommGroup M]
  [DecidableEq M] (F : c.WeightedFrame ι M)

/-- The coordinate of a vector along the frame vector `vec i`. -/
def coord (i : ι) : CayleyVector K →ₗ[K] K := c.form.flip (F.vec (F.dual i))

theorem coord_apply (i : ι) (z : CayleyVector K) :
    F.coord i z = c.form z (F.vec (F.dual i)) := rfl

theorem dual_injective : Function.Injective F.dual := fun i j h => by
  rw [← F.dual_dual i, h, F.dual_dual]

theorem coord_vec (i j : ι) : F.coord i (F.vec j) = if i = j then 1 else 0 := by
  rw [coord_apply, F.form_vec]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (fun h' => h (F.dual_injective h')), if_neg h]

theorem vec_ne_zero (i : ι) : F.vec i ≠ 0 := by
  intro h
  have h1 := F.form_vec i (F.dual i)
  rw [h, map_zero, LinearMap.zero_apply, if_pos rfl] at h1
  exact zero_ne_one h1

theorem linearIndependent : LinearIndependent K F.vec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (F.coord i) hg
  simpa [map_sum, map_smul, coord_vec, Finset.sum_ite_eq] using h

theorem span_eq_top : Submodule.span K (Set.range F.vec) = ⊤ :=
  F.linearIndependent.span_eq_top_of_card_eq_finrank' (by rw [F.card_eq, Module.finrank_fin_fun])

/-- Every vector is the sum of its frame coordinates times the frame vectors. -/
theorem sum_coord_smul (z : CayleyVector K) : ∑ i, F.coord i z • F.vec i = z := by
  have hz : z ∈ Submodule.span K (Set.range F.vec) := F.span_eq_top ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hz
  have hc : ∀ i, F.coord i z = g i := by
    intro i
    rw [← hg]
    simp [map_sum, map_smul, coord_vec, Finset.sum_ite_eq]
  simp only [hc]
  exact hg

theorem eq_of_coord_eq {z z' : CayleyVector K} (h : ∀ i, F.coord i z = F.coord i z') :
    z = z' := by
  rw [← F.sum_coord_smul z, ← F.sum_coord_smul z']
  simp only [h]

/-- The projection onto the span of the frame vectors of weight `m`. -/
def projLin (m : M) : CayleyVector K →ₗ[K] CayleyVector K :=
  ∑ i ∈ Finset.univ.filter (fun i => F.weight i = m), (F.coord i).smulRight (F.vec i)

theorem projLin_apply (m : M) (z : CayleyVector K) :
    F.projLin m z = ∑ i ∈ Finset.univ.filter (fun i => F.weight i = m), F.coord i z • F.vec i := by
  simp [projLin, LinearMap.sum_apply, LinearMap.smulRight_apply]

theorem coord_projLin (m : M) (i : ι) (z : CayleyVector K) :
    F.coord i (F.projLin m z) = if F.weight i = m then F.coord i z else 0 := by
  rw [projLin_apply, map_sum]
  simp only [map_smul, coord_vec, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A vector whose coordinates of weight different from `m` vanish is fixed by the
projection of weight `m`. -/
theorem projLin_of_coord {m : M} {z : CayleyVector K}
    (h : ∀ i, F.weight i ≠ m → F.coord i z = 0) : F.projLin m z = z := by
  apply F.eq_of_coord_eq
  intro i
  rw [coord_projLin]
  split_ifs with hi
  · rfl
  · exact (h i hi).symm

theorem projLin_comp_projLin (m n : M) :
    (F.projLin m).comp (F.projLin n) = if m = n then F.projLin m else 0 := by
  apply LinearMap.ext
  intro z
  apply F.eq_of_coord_eq
  intro i
  rw [LinearMap.comp_apply, coord_projLin, coord_projLin]
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl, coord_projLin]
    split_ifs <;> rfl
  · rw [if_neg hmn, LinearMap.zero_apply, map_zero]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) hmn
    · rfl
    · rfl

theorem sum_projLin : ∑ m ∈ Finset.univ.image F.weight, F.projLin m = LinearMap.id := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  simp only [projLin_apply]
  rw [Finset.sum_fiberwise_of_maps_to
    (fun i _ => Finset.mem_image_of_mem F.weight (Finset.mem_univ i))]
  exact F.sum_coord_smul z

/-- Products of frame vectors are homogeneous of the sum of the weights. -/
theorem projLin_mul_vec (i j : ι) :
    F.projLin (F.weight i + F.weight j) (μ (F.vec i) (F.vec j)) = μ (F.vec i) (F.vec j) := by
  apply F.projLin_of_coord
  intro l hl
  rw [coord_apply]
  apply F.form_mul
  rw [F.weight_dual]
  intro h
  apply hl
  rw [← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

/-- The projection matrices of the frame. -/
def proj (m : M) : Matrix (Fin 8) (Fin 8) K := LinearMap.toMatrix' (F.projLin m)

theorem proj_mulVec (m : M) (z : CayleyVector K) : F.proj m *ᵥ z = F.projLin m z :=
  LinearMap.toMatrix'_mulVec _ _

/-- **The grading of a weighted self-dual frame.** -/
def toGrading : c.Grading M where
  proj := F.proj
  support := Finset.univ.image F.weight
  mem_support m := by
    constructor
    · intro hm h0
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
      have h := F.proj_mulVec (F.weight i) (F.vec i)
      rw [h0, Matrix.zero_mulVec, F.projLin_of_coord] at h
      · exact F.vec_ne_zero i h.symm
      · intro j hj
        rw [coord_vec, if_neg]
        rintro rfl
        exact hj rfl
    · intro h
      by_contra hm
      apply h
      have h0 : F.projLin m = 0 := by
        rw [projLin]
        apply Finset.sum_eq_zero
        intro i hi
        exact absurd (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩) hm
      rw [proj, h0, map_zero]
  sum_proj := by
    simp only [proj]
    rw [← map_sum, F.sum_projLin, LinearMap.toMatrix'_id]
  proj_mul_proj m n := by
    simp only [proj]
    rw [← LinearMap.toMatrix'_comp, F.projLin_comp_projLin]
    split_ifs
    · rfl
    · exact map_zero _
  proj_unit := by
    rw [proj_mulVec]
    apply F.projLin_of_coord
    intro i hi
    rw [coord_apply]
    apply F.form_unit
    rw [F.weight_dual]
    exact neg_ne_zero.mpr hi
  proj_mul a b x y hx hy := by
    rw [proj_mulVec] at hx hy ⊢
    have key : ∀ i ∈ Finset.univ.filter (fun i => F.weight i = a),
        ∀ j ∈ Finset.univ.filter (fun j => F.weight j = b),
          F.projLin (a + b) (μ (F.vec i) (F.vec j)) = μ (F.vec i) (F.vec j) := by
      intro i hi j hj
      rw [← (Finset.mem_filter.mp hi).2, ← (Finset.mem_filter.mp hj).2]
      exact F.projLin_mul_vec i j
    rw [← hx, ← hy, F.projLin_apply a x, F.projLin_apply b y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    first
      | exact key i hi j hj
      | exact key j hj i hi

@[simp] theorem toGrading_support : F.toGrading.support = Finset.univ.image F.weight := rfl

end WeightedFrame

end Langlands.GroupScheme.CayleyDatum
