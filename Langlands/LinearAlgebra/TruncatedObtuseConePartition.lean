import Langlands.LinearAlgebra.ObtuseBasisDecomposition

/-! # A truncated negative cone partition for an obtuse basis -/

noncomputable section

set_option autoImplicit false

namespace Langlands.LinearAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ E) (B : LinearMap.BilinForm ℝ E)

omit [Fintype ι] [DecidableEq ι] in
/-- The translated negative coordinate cone on the common orthogonal space of `I`.
Only the coordinates outside `I` enter the upper cutoff. -/
def basisNegativeCut (I : Set ι) (s : E) : Set E :=
  {x | basisOrthogonal b B I x ∧ ∀ j ∉ I, b.coord j (x - s) ≤ 0}

omit [Fintype ι] [DecidableEq ι] in
/-- A point of the truncated cone written as a closed chamber term `y` minus a
root-cone term `z`. The positive coordinates of `z` outside `I` index the open
face of the negative cone, while the upper cutoff on `y` uses the remaining
coordinates outside `Q`. -/
def IsTruncatedBasisConeDecomposition (I : Set ι) (s x : E) (Q : Set ι) (y z : E) : Prop :=
  I ⊆ Q ∧ x = y - z ∧ basisClosedFace b B Q y ∧
    (∀ j ∉ Q, b.coord j (y - s) ≤ 0) ∧ basisOrthogonal b B I z ∧
    (∀ j ∈ Q \ I, 0 < b.coord j z) ∧ (∀ j ∉ Q, b.coord j z = 0)

variable (hs : ∀ x y, B x y = B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x)
  (ho : ∀ i j, i ≠ j → B (b i) (b j) ≤ 0)

include hp ho in
private theorem truncatedDecomposition_polar
    {I Q : Set ι} {s x y z : E} (h : IsTruncatedBasisConeDecomposition b B I s x Q y z) :
    z ∈ basisNonnegCone b Q ∧ B y z = 0 := by
  obtain ⟨_, _, ⟨hy, _⟩, _, horth, hpos, hzero⟩ := h
  have hn : ∀ j, 0 ≤ b.coord j z := by
    apply coordinates_nonneg_of_obtuse b B hp ho z
    intro j hj
    by_cases hi : j ∈ I
    · exact (horth j hi).ge
    · by_cases hq : j ∈ Q
      · exact (hj.not_gt (hpos j ⟨hq, hi⟩)).elim
      · exact (hj.ne (hzero j hq)).elim
  have hz : z ∈ basisNonnegCone b Q := fun j => ⟨hn j, hzero j⟩
  exact ⟨hz, form_zero_of_mem_basisCone b B hy hz⟩

include hp ho in
private theorem truncatedDecomposition_unique
    {I Q Q' : Set ι} {s x y z y' z' : E}
    (h : IsTruncatedBasisConeDecomposition b B I s x Q y z)
    (h' : IsTruncatedBasisConeDecomposition b B I s x Q' y' z') :
    Q' = Q ∧ y' = y ∧ z' = z := by
  obtain ⟨hz, hyz⟩ := truncatedDecomposition_polar b B hp ho h
  obtain ⟨hz', hyz'⟩ := truncatedDecomposition_polar b B hp ho h'
  have hfull {K : Set ι} {v : E} (hv : v ∈ basisNonnegCone b K) :
      v ∈ basisNonnegCone b Set.univ := fun j => ⟨(hv j).1, by simp⟩
  obtain ⟨hIQ, hsum, ⟨_, hy⟩, _, _, hpos, hzero⟩ := h
  obtain ⟨hIQ', hsum', ⟨_, hy'⟩, _, _, hpos', hzero'⟩ := h'
  obtain ⟨he, hf⟩ := basis_polar_unique b B hp hsum hsum' hy hy'
    (hfull hz) (hfull hz') hyz hyz'
  refine ⟨?_, he, hf⟩
  ext j
  by_cases hj : j ∈ I
  · exact iff_of_true (hIQ' hj) (hIQ hj)
  · constructor
    · intro hq'
      by_contra hq
      have hposj := hpos' j ⟨hq', hj⟩
      rw [hf, hzero j hq] at hposj
      exact lt_irrefl _ hposj
    · intro hq
      by_contra hq'
      have hposj := hpos j ⟨hq, hj⟩
      rw [← hf, hzero' j hq'] at hposj
      exact lt_irrefl _ hposj

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinate form of Delorme (7.26). A dominant increment cuts out a
translated negative cone. Its points have a unique lower-rank negative face
and complementary closed chamber satisfying the upper cutoff. -/
def TruncatedBasisConePartitionStatement : Prop :=
  (∀ x y, B x y = B y x) → (∀ x, x ≠ 0 → 0 < B x x) →
  (∀ i j, i ≠ j → B (b i) (b j) ≤ 0) →
  ∀ (I : Set ι) (s : E), (∀ j, 0 ≤ B s (b j)) → ∀ x : E,
    x ∈ basisNegativeCut b B I s ↔ ∃! w : Set ι × E × E,
      IsTruncatedBasisConeDecomposition b B I s x w.1 w.2.1 w.2.2

/-- Use complementary polar components and recover the face from the positive
root coordinates outside the initial orthogonal space. -/
theorem truncatedBasisConePartition : TruncatedBasisConePartitionStatement b B := by
  intro hsym hpos hobt I s hsdom x
  constructor
  · intro hx
    obtain ⟨y, z, he, hy, hz, hcomp⟩ := exists_basis_polar_decomposition b B hsym hpos x
    let Q : Set ι := I ∪ {j | 0 < b.coord j z}
    have hyI : basisOrthogonal b B I y := by
      intro j hj
      by_contra hne
      have hpos' := lt_of_le_of_ne (hy j) (fun e => hne e.symm)
      have hzj := (mul_eq_zero.mp (hcomp j)).resolve_left hne
      have hz' := form_nonpos_of_zero_coord b B hobt hz j hzj
      have horth := hx.1 j hj
      rw [he, map_sub, LinearMap.sub_apply] at horth
      linarith
    have hzI : basisOrthogonal b B I z := by
      intro j hj
      have horth := hx.1 j hj
      rw [he, map_sub, LinearMap.sub_apply, hyI j hj, zero_sub, neg_eq_zero] at horth
      exact horth
    have hyQ : basisOrthogonal b B Q y := by
      rintro j (hj | hj)
      · exact hyI j hj
      · exact (mul_eq_zero.mp (hcomp j)).resolve_right (ne_of_gt hj)
    have hnQ (j : ι) (hj : j ∉ Q) : b.coord j z = 0 := by
      have hn : ¬ 0 < b.coord j z := fun h => hj (Or.inr h)
      exact (not_lt.mp hn).antisymm (hz j)
    have hsQ (j : ι) (hj : j ∉ Q) : b.coord j (y - s) ≤ 0 := by
      have hcut := hx.2 j (fun h => hj (Or.inl h))
      rw [he, map_sub (b.coord j), map_sub (b.coord j), hnQ j hj, sub_zero] at hcut
      simpa only [map_sub] using hcut
    have hpQ (j : ι) (hj : j ∈ Q \ I) : 0 < b.coord j z := hj.1.resolve_left hj.2
    have h : IsTruncatedBasisConeDecomposition b B I s x Q y z :=
      ⟨Set.subset_union_left, he, ⟨hyQ, hy⟩, hsQ, hzI, hpQ, hnQ⟩
    refine ⟨(Q, y, z), h, ?_⟩
    rintro ⟨Q', y', z'⟩ h'
    change IsTruncatedBasisConeDecomposition b B I s x Q' y' z' at h'
    obtain ⟨hQ', hy', hz'⟩ := truncatedDecomposition_unique b B hpos hobt h h'
    rw [hQ', hy', hz']
  · rintro ⟨⟨Q, y, z⟩, h, _⟩
    change IsTruncatedBasisConeDecomposition b B I s x Q y z at h
    have hneg := (truncatedDecomposition_polar b B hpos hobt h).1
    obtain ⟨hIQ, rfl, ⟨hy, hyn⟩, hcut, hz, hposz, hzero⟩ := h
    have hc : ∀ j, 0 ≤ b.coord j (s - y) := by
      apply coordinates_nonneg_of_obtuse b B hpos hobt (s - y)
      intro j hj
      by_cases hq : j ∈ Q
      · simpa only [map_sub, LinearMap.sub_apply, hy j hq, sub_zero] using hsdom j
      · have h' := hcut j hq
        rw [map_sub] at h' hj
        linarith
    refine ⟨fun j hj => ?_, fun j _ => ?_⟩
    · rw [map_sub, LinearMap.sub_apply, hy j (hIQ hj), hz j hj, sub_self]
    · have hc' := hc j
      rw [map_sub] at hc'
      simp only [map_sub]
      linarith [(hneg j).1]

end Langlands.LinearAlgebra
