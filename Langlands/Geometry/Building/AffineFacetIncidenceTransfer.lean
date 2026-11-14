import Langlands.Geometry.Building.FacetClosurePullback

/-! # Transfer of facet incidence along an affine map preserving facets

Let `a : A₁ → A₂` be an affine map between real affine spaces carrying affine
root sets `Ψ₁` and `Ψ₂`, such that the preimage of the `Ψ₂`-facet of `a w` is
the `Ψ₁`-facet of `w` for every `w`. Then `a` carries facet closures into facet
closures, and a face of a facet is carried into a face of a facet.
-/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

open scoped Affine

variable {V : Type*} {A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {V₂ : Type*} {A₂ : Type*} [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ A₂]

/-- If an affine function has the sign of its value at `x` on the whole
half-open segment from `y` to `x`, then `y` satisfies the facet-closure sign
condition for that function. -/
theorem sign_eq_zero_or_eq_of_lineMap {ψ : A →ᵃ[ℝ] ℝ} {x y : A}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 →
      SignType.sign (ψ (AffineMap.lineMap y x t)) = SignType.sign (ψ x)) :
    SignType.sign (ψ y) = 0 ∨ SignType.sign (ψ y) = SignType.sign (ψ x) := by
  have hval : ∀ t : ℝ, ψ (AffineMap.lineMap y x t) = ψ y + t * (ψ x - ψ y) := by
    intro t
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    simp only [smul_eq_mul]
    ring
  by_contra hne
  obtain ⟨hy0, hyx⟩ := not_or.mp hne
  rw [sign_eq_zero_iff] at hy0
  rcases eq_or_ne (ψ x) 0 with hx | hx
  · have h2 := h (1 / 2) (by norm_num) (by norm_num)
    rw [hval, hx] at h2
    rw [sign_zero, sign_eq_zero_iff] at h2
    exact hy0 (by linarith)
  · -- `ψ y` and `ψ x` have opposite signs, so the segment meets the zero set.
    have hopp : ψ y * ψ x < 0 := by
      rcases lt_or_gt_of_ne hy0 with hy | hy <;> rcases lt_or_gt_of_ne hx with hx' | hx'
      · exact absurd (by rw [sign_neg hy, sign_neg hx']) hyx
      · exact mul_neg_of_neg_of_pos hy hx'
      · exact mul_neg_of_pos_of_neg hy hx'
      · exact absurd (by rw [sign_pos hy, sign_pos hx']) hyx
    have hd : ψ y - ψ x ≠ 0 := by
      intro hd
      have : ψ y = ψ x := sub_eq_zero.mp hd
      rw [this] at hopp
      nlinarith [mul_self_nonneg (ψ x)]
    set t := ψ y / (ψ y - ψ x) with ht
    have hpos : 0 < t := by
      rcases lt_or_gt_of_ne hy0 with hy | hy
      · have : ψ y - ψ x < 0 := by nlinarith
        exact div_pos_of_neg_of_neg hy this
      · have : 0 < ψ y - ψ x := by nlinarith
        exact div_pos hy this
    have hle : t ≤ 1 := by
      rcases lt_or_gt_of_ne hy0 with hy | hy
      · have hneg : ψ y - ψ x < 0 := by nlinarith
        rw [ht, div_le_one_of_neg hneg]
        nlinarith
      · have hpos' : 0 < ψ y - ψ x := by nlinarith
        rw [ht, div_le_one hpos']
        nlinarith
    have h0 := h t hpos hle
    have hz : ψ y + t * (ψ x - ψ y) = 0 := by
      rw [ht]
      field_simp
      ring
    rw [hval, hz, sign_zero] at h0
    exact hx (sign_eq_zero_iff.mp h0.symm)

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Ψ₂ : Set (A₂ →ᵃ[ℝ] ℝ)} {a : A →ᵃ[ℝ] A₂}

/-- An affine map whose facet preimages are facets carries the closure of the
facet of `x` into the closure of the facet of `a x`. -/
theorem map_mem_facetClosure
    (ha : ∀ w : A, a ⁻¹' facet Ψ₂ (a w) = facet Ψ w) {x y : A}
    (hy : y ∈ facetClosure Ψ x) : a y ∈ facetClosure Ψ₂ (a x) := by
  intro ψ hψ
  refine sign_eq_zero_or_eq_of_lineMap (ψ := ψ) fun t ht0 ht1 => ?_
  have hmem : AffineMap.lineMap y x t ∈ a ⁻¹' facet Ψ₂ (a x) := by
    rw [ha x]
    exact lineMap_mem_facet_of_mem_facetClosure hy ht0 ht1
  rw [Set.mem_preimage, AffineMap.apply_lineMap] at hmem
  exact (hmem ψ hψ).symm

/-- **Transfer of facet incidence.** Let `Fa` be a face of `Fa'` for `Ψ`, and
`x ∈ Fa`. Then there is `x₁` with facet `Fa'` such that the `Ψ₂`-facet of
`a x` is a face of the `Ψ₂`-facet of `a x₁`, and `a` carries `Fa` and `Fa'`
into these two facets. -/
theorem exists_isFaceOf_image
    (ha : ∀ w : A, a ⁻¹' facet Ψ₂ (a w) = facet Ψ w) {Fa Fa' : Set A}
    (hF : IsFaceOf Ψ Fa Fa') {x : A} (hx : x ∈ Fa) :
    ∃ x₁ : A, facet Ψ x₁ = Fa' ∧
      IsFaceOf Ψ₂ (facet Ψ₂ (a x)) (facet Ψ₂ (a x₁)) ∧
      a '' Fa ⊆ facet Ψ₂ (a x) ∧ a '' Fa' ⊆ facet Ψ₂ (a x₁) := by
  obtain ⟨⟨x₀, hx₀⟩, x₁, hx₁, hsub⟩ := hF
  have hFa : Fa = facet Ψ x := by
    rw [← hx₀] at hx ⊢
    exact (facet_eq_of_mem hx).symm
  refine ⟨x₁, hx₁, ⟨isFacet_facet _ _, a x₁, rfl, ?_⟩, ?_, ?_⟩
  · exact facet_subset_facetClosure_iff.mpr (map_mem_facetClosure ha (hsub hx))
  · rintro _ ⟨z, hz, rfl⟩
    rw [hFa, ← ha x] at hz
    exact hz
  · rintro _ ⟨z, hz, rfl⟩
    rw [← hx₁, ← ha x₁] at hz
    exact hz

end Langlands.Geometry.Building.AffineRootSystem
