import Langlands.Geometry.Building.AffineTorsorFacetVertices
import Mathlib.Analysis.Convex.Combination

/-! # Centroids and least original faces in affine root arrangements -/

noncomputable section

universe u v w z

namespace Langlands.Geometry.Building.AffineRootSystem

open Set

private theorem weakSign_average {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {a r : ℝ} (hr : 0 < r)
    (hf : ∀ i ∈ s, SignType.sign (f i) = 0 ∨ SignType.sign (f i) = SignType.sign a) :
    (SignType.sign (r * ∑ i ∈ s, f i) = 0 ∨
      SignType.sign (r * ∑ i ∈ s, f i) = SignType.sign a) ∧
    ∀ i ∈ s, SignType.sign (f i) = 0 ∨
      SignType.sign (f i) = SignType.sign (r * ∑ j ∈ s, f j) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hnonpos : ∀ i ∈ s, f i ≤ 0 := by
      intro i hi
      rcases hf i hi with hz | hn
      · exact (sign_eq_zero_iff.mp hz).le
      · rw [sign_neg ha, sign_eq_neg_one_iff] at hn
        exact hn.le
    have hd : r * ∑ i ∈ s, f i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hr.le (Finset.sum_nonpos hnonpos)
    constructor
    · rcases lt_or_eq_of_le hd with hd | hd
      · exact Or.inr ((sign_neg hd).trans (sign_neg ha).symm)
      · exact Or.inl (sign_eq_zero_iff.mpr hd)
    · intro i hi
      rcases lt_or_eq_of_le (hnonpos i hi) with hi' | hi'
      · have hsum : 0 < ∑ j ∈ s, -f j :=
          (Finset.sum_pos_iff_of_nonneg (fun j hj => neg_nonneg.mpr (hnonpos j hj))).mpr
            ⟨i, hi, neg_pos.mpr hi'⟩
        have hd' : r * ∑ j ∈ s, f j < 0 := by
          rw [Finset.sum_neg_distrib] at hsum
          exact mul_neg_of_pos_of_neg hr (neg_pos.mp hsum)
        exact Or.inr ((sign_neg hi').trans (sign_neg hd').symm)
      · exact Or.inl (sign_eq_zero_iff.mpr hi')
  · have hz : ∀ i ∈ s, f i = 0 := by
      intro i hi
      apply sign_eq_zero_iff.mp
      simpa only [ha, sign_zero, or_self] using hf i hi
    have hd : r * ∑ i ∈ s, f i = 0 := by rw [Finset.sum_eq_zero hz, mul_zero]
    exact ⟨Or.inl (sign_eq_zero_iff.mpr hd),
      fun i hi => Or.inl (sign_eq_zero_iff.mpr (hz i hi))⟩
  · have hnonneg : ∀ i ∈ s, 0 ≤ f i := by
      intro i hi
      rcases hf i hi with hz | hp
      · exact (sign_eq_zero_iff.mp hz).symm.le
      · rw [sign_pos ha, sign_eq_one_iff] at hp
        exact hp.le
    have hd : 0 ≤ r * ∑ i ∈ s, f i :=
      mul_nonneg hr.le (Finset.sum_nonneg hnonneg)
    constructor
    · rcases lt_or_eq_of_le hd with hd | hd
      · exact Or.inr ((sign_pos hd).trans (sign_pos ha).symm)
      · exact Or.inl (sign_eq_zero_iff.mpr hd.symm)
    · intro i hi
      rcases lt_or_eq_of_le (hnonneg i hi) with hi' | hi'
      · have hsum : 0 < ∑ j ∈ s, f j :=
          (Finset.sum_pos_iff_of_nonneg hnonneg).mpr ⟨i, hi, hi'⟩
        exact Or.inr ((sign_pos hi').trans (sign_pos (mul_pos hr hsum)).symm)
      · exact Or.inl (sign_eq_zero_iff.mpr hi'.symm)

section Algebra

variable {V : Type u} {A : Type v}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Evaluation of an affine functional at a nonempty finite centroid. -/
theorem affineMap_centroid_eq_average (s : Finset A) (hs : s.Nonempty)
    (ψ : A →ᵃ[ℝ] ℝ) :
    ψ (s.centroid ℝ id) = (s.card : ℝ)⁻¹ * ∑ x ∈ s, ψ x := by
  rw [Finset.centroid_def, s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) ψ,
    affineCombination_eq_centerMass (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs),
    s.centerMass_eq_of_sum_1 _ (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, Function.comp_apply, id_eq, smul_eq_mul,
    Finset.mul_sum]

/-- Averaging points in one original closed facet stays in that closed facet. -/
theorem centroid_mem_facetClosure (s : Finset A) (hs : s.Nonempty) {p : A}
    (hsp : ∀ x ∈ s, x ∈ facetClosure Ψ p) :
    s.centroid ℝ id ∈ facetClosure Ψ p := by
  intro ψ hψ
  rw [affineMap_centroid_eq_average s hs ψ]
  exact (weakSign_average s ψ
    (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hs)))
    (fun x hx => hsp x hx ψ hψ)).1

/-- No cancellation of root signs: every point of a finite set in one closed
facet lies in the original closed facet of its centroid. -/
theorem mem_facetClosure_centroid (s : Finset A) (hs : s.Nonempty) {p : A}
    (hsp : ∀ x ∈ s, x ∈ facetClosure Ψ p) :
    ∀ x ∈ s, x ∈ facetClosure Ψ (s.centroid ℝ id) := by
  intro x hx ψ hψ
  rw [affineMap_centroid_eq_average s hs ψ]
  exact (weakSign_average s ψ
    (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hs)))
    (fun y hy => hsp y hy ψ hψ)).2 x hx

/-- The centroid of a finite nonempty set in one closed facet belongs to any
original closed facet exactly when all the points do. -/
theorem centroid_mem_facetClosure_iff (s : Finset A) (hs : s.Nonempty) {p : A}
    (hsp : ∀ x ∈ s, x ∈ facetClosure Ψ p) (q : A) :
    s.centroid ℝ id ∈ facetClosure Ψ q ↔
      ∀ x ∈ s, x ∈ facetClosure Ψ q := by
  refine ⟨fun hq x hx => mem_facetClosure_trans hq
    (mem_facetClosure_centroid s hs hsp x hx),
    fun hq => centroid_mem_facetClosure s hs hq⟩

/-- The original closed facet of the centroid is the least original closed
facet containing a finite nonempty set that lies in one closed facet. -/
theorem facetClosure_centroid_subset_iff (s : Finset A) (hs : s.Nonempty) {p : A}
    (hsp : ∀ x ∈ s, x ∈ facetClosure Ψ p) (q : A) :
    facetClosure Ψ (s.centroid ℝ id) ⊆ facetClosure Ψ q ↔
      ∀ x ∈ s, x ∈ facetClosure Ψ q := by
  rw [facetClosure_subset_facetClosure_iff, centroid_mem_facetClosure_iff s hs hsp q]

/-- Affine equivalences commute with centroids of nonempty finite sets. -/
theorem affineEquiv_centroid_map
    {W : Type w} {C : Type z} [AddCommGroup W] [Module ℝ W] [AddTorsor W C]
    (e : A ≃ᵃ[ℝ] C) (s : Finset A) (hs : s.Nonempty) :
    e (s.centroid ℝ id) = (s.map e.toEquiv.toEmbedding).centroid ℝ id := by
  rw [Finset.centroid_map, Finset.centroid_def, Finset.centroid_def]
  exact s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) e.toAffineMap

end Algebra

section FiniteVertices

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- The canonical centroid of all actual vertices incident to an original facet. -/
def facetCentroid (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) : A :=
  (torsorFacetClosureVertexFinset hΨ p).centroid ℝ id

/-- The canonical centroid belongs to the original open facet, including in rank zero. -/
theorem facetCentroid_mem_facet (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) :
    facetCentroid hΨ p ∈ facet Ψ p := by
  let s := torsorFacetClosureVertexFinset hΨ p
  have hs : s.Nonempty := torsorFacetClosureVertexFinset_nonempty hΨ p
  have hsp : ∀ x ∈ s, x ∈ facetClosure Ψ p :=
    fun x hx => ((mem_torsorFacetClosureVertexFinset hΨ p x).mp hx).1
  have hcp : facetCentroid hΨ p ∈ facetClosure Ψ p :=
    centroid_mem_facetClosure s hs hsp
  have hpc : p ∈ facetClosure Ψ (facetCentroid hΨ p) := by
    apply facetClosure_subset_facetClosure_iff.mp
    apply (torsorFacetClosureVertexFinset_subset_iff hΨ p (facetCentroid hΨ p)).mp
    intro x hx
    apply (mem_torsorFacetClosureVertexFinset hΨ (facetCentroid hΨ p) x).mpr
    exact ⟨mem_facetClosure_centroid s hs hsp x hx,
      ((mem_torsorFacetClosureVertexFinset hΨ p x).mp hx).2⟩
  apply facetClosure_eq_facetClosure_iff.mp
  exact Set.Subset.antisymm
    (facetClosure_subset_facetClosure_iff.mpr hpc)
    (facetClosure_subset_facetClosure_iff.mpr hcp)

/-- The canonical centroid depends only on the original facet class. -/
theorem facetCentroid_eq_of_facetRel (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {p q : A} (hpq : facetRel Ψ p q) :
    facetCentroid hΨ p = facetCentroid hΨ q := by
  unfold facetCentroid
  rw [(torsorFacetClosureVertexFinset_eq_iff hΨ p q).mpr hpq]

/-- Canonical centroids agree exactly for points in the same original facet. -/
theorem facetCentroid_eq_iff (hΨ : IsAffineRootSystemWithRankZero Ψ) (p q : A) :
    facetCentroid hΨ p = facetCentroid hΨ q ↔ facetRel Ψ p q := by
  refine ⟨fun he => ?_, facetCentroid_eq_of_facetRel hΨ⟩
  have hp := facetCentroid_mem_facet hΨ p
  rw [he] at hp
  exact (facetRel_equivalence Ψ).trans hp
    ((facetRel_equivalence Ψ).symm (facetCentroid_mem_facet hΨ q))

/-- Choosing the canonical centroid twice has the same result. -/
theorem facetCentroid_idempotent (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) :
    facetCentroid hΨ (facetCentroid hΨ p) = facetCentroid hΨ p :=
  facetCentroid_eq_of_facetRel hΨ
    ((facetRel_equivalence Ψ).symm (facetCentroid_mem_facet hΨ p))

end FiniteVertices

section Transport

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddTorsor V A]
  {W : Type w} {C : Type z}
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [AddTorsor W C]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Full affine root transport carries the entire finite set of actual facet
vertices to the corresponding original finite set. -/
theorem torsorFacetClosureVertexFinset_transportedRoots
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (e : A ≃ᵃ[ℝ] C) (p : A) :
    torsorFacetClosureVertexFinset (hΨ.transport e) (e p) =
      (torsorFacetClosureVertexFinset hΨ p).map e.toEquiv.toEmbedding := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [mem_torsorFacetClosureVertexFinset, Finset.mem_map_equiv]
  change _ ↔ e.symm (e x) ∈ torsorFacetClosureVertexFinset hΨ p
  rw [e.symm_apply_apply, mem_torsorFacetClosureVertexFinset,
    mem_facetClosure_transportedRoots_iff, isVertex_transportedRoots_iff]

/-- The canonical centroid is natural under full affine root transport. -/
theorem facetCentroid_transportedRoots (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (e : A ≃ᵃ[ℝ] C) (p : A) :
    facetCentroid (hΨ.transport e) (e p) = e (facetCentroid hΨ p) := by
  unfold facetCentroid
  rw [torsorFacetClosureVertexFinset_transportedRoots]
  exact (affineEquiv_centroid_map e _
    (torsorFacetClosureVertexFinset_nonempty hΨ p)).symm

end Transport

end Langlands.Geometry.Building.AffineRootSystem
