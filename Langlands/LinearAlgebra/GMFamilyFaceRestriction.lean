import Langlands.LinearAlgebra.GMFamilyChamberCoordinates
import Langlands.LinearAlgebra.GMFamiliesFaces

/-! # Restricting `(G, M)`-families to the Levi subgroup of a face

For a face `Q = posSet R w` (`w ∈ a`) the roots of `M_Q` form the root set `leviRoots R Q`, the
space `a` is again one of its Levi spaces, and `S ↦ c (Q ∪ S)` is a `(M_Q, M)`-family whenever
`c` is a `(G, M)`-family. The simple roots of a chamber `S` of `M_Q` are the simple roots of
`Q ∪ S` that vanish at `w`. -/

noncomputable section

open scoped RealInnerProductSpace
open Finset Classical

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

/-- `a` is a Levi space for the roots of the Levi subgroup of a face of `a`. -/
theorem isLeviSpace_leviRoots (ha : IsLeviSpace R a) (w : a) :
    IsLeviSpace (leviRoots R (posSet R (w : E))) a := by
  obtain ⟨h₀, hh₀⟩ := exists_regular_point R a
  have hap := ha.eq_leviSpaceOf_of_regular hh₀
  refine ⟨h₀, hap.trans ?_⟩
  have hfilter : (leviRoots R (posSet R (w : E))).filter (fun α => ⟪α, h₀⟫ = 0) =
      R.filter (fun α => ⟪α, h₀⟫ = 0) := by
    ext α
    simp only [Finset.mem_filter, leviRoots, mem_posSet]
    constructor
    · rintro ⟨⟨hα, -⟩, hz⟩
      exact ⟨hα, hz⟩
    · rintro ⟨hα, hz⟩
      have hw : ⟪α, (w : E)⟫ = 0 := by
        have hwa : (w : E) ∈ leviSpaceOf R h₀ := hap ▸ w.property
        exact (mem_leviSpaceOf_iff.mp hwa) α hα hz
      refine ⟨⟨hα, ?_, ?_⟩, hz⟩
      · rintro ⟨-, hp⟩
        rw [hw] at hp
        exact lt_irrefl _ hp
      · rintro ⟨-, hp⟩
        rw [inner_neg_left, hw, neg_zero] at hp
        exact lt_irrefl _ hp
  simp only [leviSpaceOf, hfilter]

/-- The simple roots of a chamber of the Levi subgroup of the face `posSet R w` are the simple
roots of the chamber above the face that vanish at `w`. -/
theorem simpleRoots_face_eq_filter (hR : IsRootSet R) (w : a) {S : Finset E}
    (hS : S ∈ parabolics (leviRoots R (posSet R (w : E))) a) :
    simpleRoots a S = (simpleRoots a (posSet R (w : E) ∪ S)).filter (fun v => ⟪v, w⟫ = 0) := by
  obtain ⟨hP, hinter⟩ := union_parabolic_of_local hR w hS
  have h := simpleRoots_inter_leviRoots hR hP w Finset.subset_union_left
  rw [hinter] at h
  exact h

theorem simpleRoots_face_subset (hR : IsRootSet R) (w : a) {S : Finset E}
    (hS : S ∈ parabolics (leviRoots R (posSet R (w : E))) a) :
    simpleRoots a S ⊆ simpleRoots a (posSet R (w : E) ∪ S) := by
  rw [simpleRoots_face_eq_filter hR w hS]
  exact Finset.filter_subset _ _

/-- For a nonempty face `posSet R w` (a parabolic subgroup `Q ≠ G`) and a chamber `S` of its Levi
subgroup, some simple root of the chamber `posSet R w ∪ S` above it is not a simple root of `S`. -/
theorem exists_simpleRoot_not_mem_face (hR : IsRootSet R) (w : a) {S : Finset E}
    (hS : S ∈ parabolics (leviRoots R (posSet R (w : E))) a) (hQ : posSet R (w : E) ≠ ∅) :
    ∃ β ∈ simpleRoots a (posSet R (w : E) ∪ S), β ∉ simpleRoots a S := by
  by_contra! hall
  obtain ⟨hP, -⟩ := union_parabolic_of_local hR w hS
  have hzero (i : simpleRoots a (posSet R (w : E) ∪ S)) : ⟪(i : a), w⟫ = 0 := by
    have hi := hall i i.property
    rw [simpleRoots_face_eq_filter hR w hS] at hi
    exact (Finset.mem_filter.mp hi).2
  have h1 := nonneg_posSet_of_nonneg_simpleRoots hP w (fun i => (hzero i).ge)
  obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr hQ
  have hpos := (mem_posSet.mp hα).2
  have h2 := nonneg_posSet_of_nonneg_simpleRoots hP (-w) (fun i => by
    rw [inner_neg_right, hzero i, neg_zero])
  have h2' := h2 α (Finset.mem_union_left _ hα)
  simp only [Submodule.coe_neg, inner_neg_right] at h2'
  linarith

/-- Adjacent chambers of the Levi subgroup of a face give adjacent chambers above the face. -/
theorem isAdjacentAlong_face_union (hR : IsRootSet R) (w : a) {S S' : Finset E}
    (hS : S ∈ parabolics (leviRoots R (posSet R (w : E))) a)
    (hS' : S' ∈ parabolics (leviRoots R (posSet R (w : E))) a) {v : a}
    (hadj : IsAdjacentAlong (leviRoots R (posSet R (w : E))) a S S' v) :
    IsAdjacentAlong R a (posSet R (w : E) ∪ S) (posSet R (w : E) ∪ S') v := by
  refine ⟨simpleRoots_face_subset hR w hS hadj.1, simpleRoots_face_subset hR w hS' hadj.2.1,
    fun α hα hnot => ?_⟩
  have hSR : S ⊆ leviRoots R (posSet R (w : E)) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hSR' : S' ⊆ leviRoots R (posSet R (w : E)) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS').1
  by_cases hl : α ∈ leviRoots R (posSet R (w : E))
  · have hnQ : α ∉ posSet R (w : E) := (Finset.mem_filter.mp hl).2.1
    have h := hadj.2.2 α hl hnot
    simp only [Finset.mem_union, hnQ, false_or, h]
  · have h1 : α ∉ S := fun h => hl (hSR h)
    have h2 : α ∉ S' := fun h => hl (hSR' h)
    simp only [Finset.mem_union, h1, h2, or_false]

/-- **Restriction of a `(G, M)`-family to the Levi subgroup of a face.** -/
theorem isFamily_face (hR : IsRootSet R) (w : a) {c : Finset E → StrongDual ℝ a → ℂ}
    (hc : IsFamily R a c) :
    IsFamily (leviRoots R (posSet R (w : E))) a (fun S => c (posSet R (w : E) ∪ S)) := by
  refine ⟨fun S hS => hc.1 _ (union_parabolic_of_local hR w hS).1,
    fun S hS S' hS' v hadj Λ hΛ => ?_⟩
  exact hc.2 _ (union_parabolic_of_local hR w hS).1 _ (union_parabolic_of_local hR w hS').1 v
    (isAdjacentAlong_face_union hR w hS hS' hadj) Λ hΛ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The empty face: its Levi root set is the whole root set. -/
theorem leviRoots_empty (R : Finset E) : leviRoots R ∅ = R := by
  ext α
  simp [leviRoots]

/-- The Levi weight of a chamber is the chamber's own function. -/
theorem cQM_parabolic (hR : IsRootSet R) {P : Finset E} (hP : P ∈ parabolics R a)
    (c : Finset E → StrongDual ℝ a → ℂ) (Λ : StrongDual ℝ a) : cQM R a c P Λ = c P Λ := by
  rw [cQM_eq_sum_chambers hR (parabolics_subset_faces R a hP)]
  have hfilter : (parabolics R a).filter (P ⊆ ·) = {P} := by
    ext P'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hP', hsub⟩
      exact (parabolic_eq_of_subset hR hP (parabolics_subset_faces R a hP') hsub).symm
    · rintro rfl
      exact ⟨hP, Finset.Subset.refl _⟩
  rw [hfilter, Finset.sum_singleton]
  have hempty : P ∩ leviRoots R P = ∅ := by
    ext α
    simp only [Finset.mem_inter, leviRoots, Finset.mem_filter, Finset.notMem_empty, iff_false]
    tauto
  have htheta : theta a (∅ : Finset E) Λ = 1 := by
    have hs : simpleRoots a (∅ : Finset E) = ∅ := by
      simp [simpleRoots, restrictedRoots]
    have : IsEmpty (simpleRoots a (∅ : Finset E)) := by
      rw [hs]; exact Finset.isEmpty_coe_sort.mpr rfl
    simp [theta, thetaOf, gramVolume, Matrix.det_isEmpty]
  rw [hempty, htheta, inv_one, mul_one]

end Langlands.GMFamily
