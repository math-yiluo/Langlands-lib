import Langlands.Analysis.RenardConeProjectionProof
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! # Cones of an obtuse basis for a supplied positive form -/

noncomputable section

open scoped BigOperators

namespace Langlands.LinearAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Euclidean core determined by a symmetric positive definite form. -/
@[instance_reducible] def positiveFormCore (B : LinearMap.BilinForm ℝ E)
    (hs : ∀ x y, B x y = B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    InnerProductSpace.Core ℝ E where
  inner x y := B x y
  conj_inner_symm x y := hs y x
  re_inner_nonneg x := by
    by_cases h : x = 0
    · simp [h]
    · exact (hp x h).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra h
    exact (hp x h).ne' hx

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)

/-- Nonnegative basis coordinates supported in the selected index set. -/
def basisNonnegCone (S : Set ι) : PointedCone ℝ E :=
  PointedCone.ofConeComb
    {x | ∀ j, 0 ≤ b.coord j x ∧ (j ∉ S → b.coord j x = 0)}
    ⟨0, by simp⟩ (by
      intro x hx y hy a ha c hc j
      simp only [map_add, map_smul, smul_eq_mul]
      exact ⟨add_nonneg (mul_nonneg ha (hx j).1) (mul_nonneg hc (hy j).1),
        fun hj => by rw [(hx j).2 hj, (hy j).2 hj]; ring⟩)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_basisNonnegCone (S : Set ι) (x : E) :
    x ∈ basisNonnegCone b S ↔
      ∀ j, 0 ≤ b.coord j x ∧ (j ∉ S → b.coord j x = 0) := Iff.rfl

/-- The coordinate cone is the pointed hull of the selected basis vectors. -/
theorem basisNonnegCone_eq_hull (S : Set ι) :
    basisNonnegCone b S = PointedCone.hull ℝ (b '' S) := by
  apply le_antisymm
  · intro x hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : j ∈ S
    · exact PointedCone.smul_mem _ (hx j).1 (PointedCone.subset_hull ⟨j, hj, rfl⟩)
    · have hz : b.repr x j = 0 := (hx j).2 hj
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩ k
    by_cases h : k = j
    · subst k
      simpa using (show (0 : ℝ) ≤ 1 ∧ (j ∉ S → (1 : ℝ) = 0) from
        ⟨zero_le_one, fun hn => (hn hj).elim⟩)
    · simp [Module.Basis.coord_apply, h]

omit [DecidableEq ι] in
/-- Supported basis coordinates characterize the selected linear span. -/
theorem mem_span_basis_iff (S : Set ι) (x : E) :
    x ∈ Submodule.span ℝ (b '' S) ↔ ∀ j ∉ S, b.coord j x = 0 := by
  constructor
  · intro hx j hj
    have hle : Submodule.span ℝ (b '' S) ≤ (b.coord j).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      simp [Module.Basis.coord_apply, show k ≠ j from fun h => hj (h ▸ hk)]
    exact hle hx
  · intro hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : j ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · have hz : b.repr x j = 0 := hx j hj
      simp [hz]

variable (B : LinearMap.BilinForm ℝ E)
    (hs : ∀ x y, B x y = B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x)

include hp in
theorem form_self_nonneg (x : E) : 0 ≤ B x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (hp x hx).le

omit [DecidableEq ι] in
/-- The root cone pairs nonnegatively with its chamber. -/
theorem form_nonneg_of_mem_basisCone {S : Set ι} {p z : E}
    (hp : ∀ j ∈ S, 0 ≤ B p (b j)) (hz : z ∈ basisNonnegCone b S) : 0 ≤ B p z := by
  rw [← b.sum_repr z, map_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [map_smul, smul_eq_mul]
  by_cases hj : j ∈ S
  · exact mul_nonneg (hz j).1 (hp j hj)
  · have he : b.repr z j = 0 := (hz j).2 hj
    simp [he]

omit [DecidableEq ι] in
/-- A face is orthogonal to the root cone on its zero indices. -/
theorem form_zero_of_mem_basisCone {S : Set ι} {p z : E}
    (hp : ∀ j ∈ S, B p (b j) = 0) (hz : z ∈ basisNonnegCone b S) : B p z = 0 := by
  rw [← b.sum_repr z, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul, smul_eq_mul]
  by_cases hj : j ∈ S
  · rw [hp j hj, mul_zero]
  · have he : b.repr z j = 0 := (hz j).2 hj
    simp [he]

include hp in
/-- For an obtuse basis, a vector whose negative coordinates have nonnegative
root pairings in fact has no negative coordinates. -/
theorem coordinates_nonneg_of_obtuse
    (ho : ∀ i j, i ≠ j → B (b i) (b j) ≤ 0) (x : E)
    (hx : ∀ j, b.coord j x < 0 → 0 ≤ B x (b j)) :
    ∀ j, 0 ≤ b.coord j x := by
  classical
  let N : Finset ι := Finset.univ.filter fun j => b.coord j x < 0
  let n : E := ∑ j ∈ N, (-b.coord j x) • b j
  let q : E := ∑ j ∈ Finset.univ \ N, b.coord j x • b j
  have hsum : x = q - n := by
    have he := Finset.sum_sdiff (s₁ := N) (s₂ := Finset.univ) (Finset.subset_univ N)
      (f := fun j => b.coord j x • b j)
    rw [← b.sum_repr x]
    simpa only [Module.Basis.coord_apply, n, q, neg_smul, Finset.sum_neg_distrib,
      sub_neg_eq_add] using he.symm
  have hxn : 0 ≤ B x n := by
    simp only [n, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_nonneg
    intro j hj
    have hneg := (Finset.mem_filter.mp hj).2
    exact mul_nonneg (neg_nonneg.mpr hneg.le) (hx j hneg)
  have hqn : B q n ≤ 0 := by
    simp only [q, n, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_nonpos
    intro j hj
    apply mul_nonpos_of_nonneg_of_nonpos
      (neg_nonneg.mpr (Finset.mem_filter.mp hj).2.le)
    apply Finset.sum_nonpos
    intro i hi
    have hiN := (Finset.mem_sdiff.mp hi).2
    have hci : 0 ≤ b.coord i x := by
      exact le_of_not_gt fun h => hiN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact mul_nonpos_of_nonneg_of_nonpos hci
      (ho i j (fun h => hiN (h ▸ hj)))
  have hn0 : n = 0 := by
    by_contra hn
    have hpos := hp n hn
    rw [hsum, map_sub, LinearMap.sub_apply] at hxn
    linarith
  intro j
  by_contra h
  have hj : j ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩
  have hncoord := congrArg (b.coord j) hn0
  simp [n, Module.Basis.coord_apply, Finsupp.single_apply, hj] at hncoord
  exact h (by rw [show b.coord j x = 0 from hncoord])

include hp in
/-- Nonnegative coordinates outside `J`, together with orthogonality on `J`,
force nonnegative coordinates everywhere for an obtuse basis. -/
theorem mem_basisCone_of_congruent_orthogonal
    (ho : ∀ i j, i ≠ j → B (b i) (b j) ≤ 0)
    {J K : Set ι} (hJK : J ⊆ K) {y z : E}
    (hy : ∀ j ∈ J, B y (b j) = 0)
    (hz : z ∈ basisNonnegCone b (K \ J))
    (hc : y - z ∈ Submodule.span ℝ (b '' J)) :
    y ∈ basisNonnegCone b K := by
  have hcoord := (mem_span_basis_iff b J (y - z)).mp hc
  have hnonneg : ∀ j, 0 ≤ b.coord j y :=
    coordinates_nonneg_of_obtuse b B hp ho y (by
      intro j hj
      by_cases hjJ : j ∈ J
      · exact (hy j hjJ).ge
      · have he : b.coord j y = b.coord j z := sub_eq_zero.mp (by
          simpa only [map_sub] using hcoord j hjJ)
        rw [he] at hj
        exact (not_lt_of_ge (hz j).1 hj).elim)
  intro j
  refine ⟨hnonneg j, fun hj => ?_⟩
  have hjJ : j ∉ J := fun h => hj (hJK h)
  have he := hcoord j hjJ
  have hz0 := (hz j).2 (fun h => hj h.1)
  simpa only [map_sub, hz0, sub_zero] using he

include hs hp in
/-- The nearest-point inequality follows algebraically from the obtuse-angle inequality. -/
theorem form_nearest_of_obtuse {C : Set E} {x p : E}
    (h : ∀ w ∈ C, B (x - p) (w - p) ≤ 0) :
    ∀ w ∈ C, B (x - p) (x - p) ≤ B (x - w) (x - w) := by
  intro w hw
  have hn := form_self_nonneg B hp (w - p)
  have he : B (x - w) (x - w) =
      B (x - p) (x - p) - 2 * B (x - p) (w - p) + B (w - p) (w - p) := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hs p x, hs w x, hs w p]
    ring
  rw [he]
  linarith [h w hw]

include hs hp in
/-- A supplied positive form and any finite basis admit a complementary
chamber/root-cone decomposition. -/
theorem exists_basis_polar_decomposition (x : E) :
    ∃ p z : E, x = p - z ∧
      (∀ j, 0 ≤ B p (b j)) ∧
      (∀ j, 0 ≤ b.coord j z) ∧
      (∀ j, B p (b j) * b.coord j z = 0) := by
  let := positiveFormCore B hs hp
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := E)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ E)
  let : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let ω : ι → E := fun j => (InnerProductSpace.toDual ℝ E).symm
    (LinearMap.toContinuousLinearMap (b.coord j))
  have hω : ∀ i j, inner ℝ (b i) (ω j) = if i = j then 1 else 0 := by
    intro i j
    rw [real_inner_comm]
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm
      (LinearMap.toContinuousLinearMap (b.coord j))) (b i) = _
    rw [InnerProductSpace.toDual_symm_apply]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  obtain ⟨⟨F, ⟨t, s, ht, hsn, he⟩, _⟩, _⟩ :=
    Langlands.Renard.coneProjectionBasisStatement ι E b ω hω x
  let p : E := ∑ i ∈ Finset.univ \ F, t i • ω i
  let z : E := ∑ j ∈ F, s j • b j
  have hpj (j : ι) : B p (b j) = if j ∈ F then 0 else t j := by
    change inner ℝ p (b j) = _
    rw [real_inner_comm]
    exact Langlands.Renard.ConeProjection.inner_basis_sum_compl b hω F t j
  have hzj (j : ι) : b.coord j z = if j ∈ F then s j else 0 := by
    simp [z, Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
  refine ⟨p, z, he, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [hpj]
    split_ifs with hj
    · exact le_rfl
    · exact (ht j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)).le
  · rw [hzj]
    split_ifs with hj
    · exact hsn j hj
    · exact le_rfl
  · rw [hpj, hzj]
    split_ifs <;> simp

end Langlands.LinearAlgebra
