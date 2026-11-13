import Langlands.LinearAlgebra.ObtuseBasisCones

/-! # Langlands decomposition for a finite obtuse basis -/

noncomputable section
open scoped BigOperators

namespace Langlands.LinearAlgebra

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ E) (B : LinearMap.BilinForm ℝ E)

/-- The common orthogonal space of selected basis vectors. -/
def basisOrthogonal (J : Set ι) (x : E) : Prop := ∀ j ∈ J, B x (b j) = 0

/-- A relatively open face of the dual chamber. -/
def basisOpenFace (K : Set ι) (p : E) : Prop :=
  (∀ j ∈ K, B p (b j) = 0) ∧ (∀ j ∉ K, 0 < B p (b j))

/-- The corresponding closed chamber in the selected orthogonal space. -/
def basisClosedFace (J : Set ι) (p : E) : Prop :=
  basisOrthogonal b B J p ∧ ∀ j, 0 ≤ B p (b j)

/-- The nonnegative root cone projected along selected basis directions. -/
def basisProjectedCone (J S : Set ι) (y : E) : Prop :=
  basisOrthogonal b B J y ∧
    ∃ z ∈ basisNonnegCone b S, y - z ∈ Submodule.span ℝ (b '' J)

/-- The basis version of the signed chamber/root decomposition. -/
def IsBasisLanglandsDecomposition (J : Set ι) (x : E) (K : Set ι) (p m : E) : Prop :=
  J ⊆ K ∧ x = p + m ∧ basisOpenFace b B K p ∧
    basisProjectedCone b B J (K \ J) (-m)

variable (hs : ∀ x y, B x y = B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x)
  (ho : ∀ i j, i ≠ j → B (b i) (b j) ≤ 0)

omit [Fintype ι] [DecidableEq ι] in
/-- Open faces belong to the full closed chamber. -/
theorem basisOpenFace_nonneg {K : Set ι} {p : E} (h : basisOpenFace b B K p) :
    ∀ j, 0 ≤ B p (b j) := by
  intro j
  by_cases hj : j ∈ K
  · exact (h.1 j hj).ge
  · exact (h.2 j hj).le

include hp ho in
/-- For an obtuse basis the projected positive cone lies in the full root cone. -/
theorem basisProjectedCone_full {J K : Set ι} (hJK : J ⊆ K) {y : E}
    (hy : basisProjectedCone b B J (K \ J) y) : y ∈ basisNonnegCone b K :=
  mem_basisCone_of_congruent_orthogonal b B hp ho hJK hy.1 hy.2.choose_spec.1
    hy.2.choose_spec.2

include ho in
/-- A nonnegative vector with zero selected coordinate has nonpositive pairing there. -/
theorem form_nonpos_of_zero_coord {z : E} (hz : ∀ j, 0 ≤ b.coord j z)
    (j : ι) (hj : b.coord j z = 0) : B z (b j) ≤ 0 := by
  rw [← b.sum_repr z, map_sum, LinearMap.sum_apply]
  apply Finset.sum_nonpos
  intro i _
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  by_cases hi : i = j
  · subst i
    simp only [show b.repr z j = 0 from hj, zero_mul]
    exact le_rfl
  · exact mul_nonpos_of_nonneg_of_nonpos (hz i) (ho i j hi)

/-- Removing coordinates in `J` gives the witness for projection along their span. -/
theorem basisProjectedCone_of_full {J K : Set ι} {z : E}
    (hz : z ∈ basisNonnegCone b K) (horth : basisOrthogonal b B J z) :
    basisProjectedCone b B J (K \ J) z := by
  classical
  let q : E := ∑ j ∈ Finset.univ.filter (fun j => j ∉ J), b.coord j z • b j
  have hq (j : ι) : b.coord j q = if j ∈ J then 0 else b.coord j z := by
    simp [q, Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
  refine ⟨horth, q, ?_, (mem_span_basis_iff b J (z - q)).mpr ?_⟩
  · intro j
    rw [hq]
    by_cases hj : j ∈ J
    · simp [hj]
    · simp only [hj, ite_false]
      refine ⟨(hz j).1, fun h => (hz j).2 ?_⟩
      exact fun hk => h ⟨hk, hj⟩
  · intro j hj
    simp only [map_sub, hq, hj, ite_false, sub_self]

include hs hp ho in
/-- Existence in every selected orthogonal space, with the same full-basis components. -/
theorem exists_basisLanglandsDecomposition (J : Set ι) (x : E)
    (hx : basisOrthogonal b B J x) :
    ∃ K p m, IsBasisLanglandsDecomposition b B J x K p m := by
  obtain ⟨p, z, he, hpn, hzn, hcomp⟩ := exists_basis_polar_decomposition b B hs hp x
  let K : Set ι := {j | B p (b j) = 0}
  have hz : z ∈ basisNonnegCone b K := by
    intro j
    exact ⟨hzn j, fun hj => (mul_eq_zero.mp (hcomp j)).resolve_left hj⟩
  have hJK : J ⊆ K := by
    intro j hj
    by_contra hn
    have hzj : b.coord j z = 0 := (hz j).2 hn
    have hnonpos := form_nonpos_of_zero_coord b B ho hzn j hzj
    have hxj := hx j hj
    rw [he, map_sub, LinearMap.sub_apply] at hxj
    have hpos : 0 < B p (b j) := lt_of_le_of_ne (hpn j) (Ne.symm hn)
    linarith
  have horth : basisOrthogonal b B J z := by
    intro j hj
    have hxj := hx j hj
    rw [he, map_sub, LinearMap.sub_apply, hJK hj] at hxj
    linarith
  refine ⟨K, p, -z, hJK, by simpa only [sub_eq_add_neg] using he, ?_, ?_⟩
  · exact ⟨fun _ hj => hj, fun j hj => lt_of_le_of_ne (hpn j) (Ne.symm hj)⟩
  · simpa only [neg_neg] using basisProjectedCone_of_full b B hz horth

include hp ho in
/-- A decomposition is a complementary full-basis polar decomposition. -/
theorem basisLanglandsDecomposition_polar {J K : Set ι} {x p m : E}
    (h : IsBasisLanglandsDecomposition b B J x K p m) :
    (∀ j, 0 ≤ B p (b j)) ∧ (-m ∈ basisNonnegCone b K) ∧ B p (-m) = 0 := by
  have hz := basisProjectedCone_full b B hp ho h.1 h.2.2.2
  exact ⟨basisOpenFace_nonneg b B h.2.2.1, hz,
    form_zero_of_mem_basisCone b B h.2.2.1.1 hz⟩

omit [DecidableEq ι] in
include hp in
/-- Complementary polar decompositions have the same two vectors. -/
theorem basis_polar_unique {x p z p' z' : E}
    (he : x = p - z) (he' : x = p' - z')
    (hpn : ∀ j, 0 ≤ B p (b j)) (hpn' : ∀ j, 0 ≤ B p' (b j))
    (hz : z ∈ basisNonnegCone b Set.univ) (hz' : z' ∈ basisNonnegCone b Set.univ)
    (hpz : B p z = 0) (hpz' : B p' z' = 0) : p' = p ∧ z' = z := by
  have hcross := form_nonneg_of_mem_basisCone b B (fun j _ => hpn j) hz'
  have hcross' := form_nonneg_of_mem_basisCone b B (fun j _ => hpn' j) hz
  have hd : p - p' = z - z' := by
    calc
      p - p' = (p - z) - (p' - z') + (z - z') := by abel
      _ = z - z' := by rw [← he, ← he']; simp
  have hn : p - p' = 0 := by
    by_contra hn
    have hpos := hp (p - p') hn
    nth_rw 2 [hd] at hpos
    simp only [map_sub, LinearMap.sub_apply, hpz, hpz'] at hpos
    linarith
  have heq : p' = p := (sub_eq_zero.mp hn).symm
  refine ⟨heq, ?_⟩
  rw [heq] at he'
  exact sub_right_inj.mp (he'.symm.trans he)

include hp ho in
/-- Uniqueness includes the index set, recovered from the zero pairings. -/
theorem basisLanglandsDecomposition_unique {J J' K K' : Set ι} {x p m p' m' : E}
    (h : IsBasisLanglandsDecomposition b B J x K p m)
    (h' : IsBasisLanglandsDecomposition b B J' x K' p' m') :
    K' = K ∧ p' = p ∧ m' = m := by
  obtain ⟨hpn, hz, hpz⟩ := basisLanglandsDecomposition_polar b B hp ho h
  obtain ⟨hpn', hz', hpz'⟩ := basisLanglandsDecomposition_polar b B hp ho h'
  have hfull {z : E} {S : Set ι} (hz : z ∈ basisNonnegCone b S) :
      z ∈ basisNonnegCone b Set.univ := fun j => ⟨(hz j).1, by simp⟩
  obtain ⟨hpp, hmm⟩ := basis_polar_unique b B hp
    (by simpa using h.2.1) (by simpa using h'.2.1) hpn hpn' (hfull hz) (hfull hz') hpz hpz'
  have hmm' : m' = m := neg_injective hmm
  refine ⟨?_, hpp, hmm'⟩
  ext j
  constructor
  · intro hj
    by_contra hn
    have hzero := h'.2.2.1.1 j hj
    rw [hpp] at hzero
    exact (h.2.2.1.2 j hn).ne' hzero
  · intro hj
    by_contra hn
    have hzero := h.2.2.1.1 j hj
    have hpos := h'.2.2.1.2 j hn
    rw [hpp, hzero] at hpos
    exact lt_irrefl _ hpos

include hp ho in
/-- Every selected-space decomposition is also its full-space decomposition. -/
theorem basisLanglandsDecomposition_empty {J K : Set ι} {x p m : E}
    (h : IsBasisLanglandsDecomposition b B J x K p m) :
    IsBasisLanglandsDecomposition b B ∅ x K p m := by
  have hz := (basisLanglandsDecomposition_polar b B hp ho h).2.1
  refine ⟨Set.empty_subset _, h.2.1, h.2.2.1, ?_⟩
  simpa only [Set.sdiff_empty] using
    basisProjectedCone_of_full b B hz (show basisOrthogonal b B ∅ (-m) from by simp [basisOrthogonal])

include hs hp ho in
/-- The positive and negative terms minimize distance to their respective closed cones. -/
theorem basisLanglandsDecomposition_projections {J K : Set ι} {x p m : E}
    (h : IsBasisLanglandsDecomposition b B J x K p m) :
    (basisClosedFace b B J p ∧ ∀ w, basisClosedFace b B J w →
      B (x - p) (x - p) ≤ B (x - w) (x - w)) ∧
    (basisProjectedCone b B J (Set.univ \ J) (-m) ∧
      ∀ w, basisProjectedCone b B J (Set.univ \ J) (-w) →
      B (x - m) (x - m) ≤ B (x - w) (x - w)) ∧ B p m = 0 := by
  obtain ⟨hpn, hz, hpz⟩ := basisLanglandsDecomposition_polar b B hp ho h
  have horth : basisOrthogonal b B J p := fun j hj => h.2.2.1.1 j (h.1 hj)
  have hzm : -m ∈ basisNonnegCone b Set.univ := fun j => ⟨(hz j).1, by simp⟩
  have hneg : B p m = 0 := by simpa only [map_neg, neg_eq_zero] using hpz
  refine ⟨⟨⟨horth, hpn⟩, ?_⟩, ⟨?_, ?_⟩, hneg⟩
  · apply form_nearest_of_obtuse B hs hp
    intro w hw
    have hn := form_nonneg_of_mem_basisCone b B (fun j _ => hw.2 j) hzm
    rw [hs w (-m), map_neg, LinearMap.neg_apply] at hn
    have he : x - p = m := by rw [h.2.1]; abel
    rw [he, map_sub, hs m p, hneg]
    linarith
  · exact basisProjectedCone_of_full b B hzm h.2.2.2.1
  · apply form_nearest_of_obtuse B hs hp
    intro w hw
    have hwfull := basisProjectedCone_full b B hp ho (Set.subset_univ J) hw
    have hn := form_nonneg_of_mem_basisCone b B (fun j _ => hpn j) hwfull
    have he : x - m = p := by rw [h.2.1]; abel
    rw [he, map_sub, hneg]
    simpa only [map_neg, neg_nonneg, sub_zero] using hn

end Langlands.LinearAlgebra
