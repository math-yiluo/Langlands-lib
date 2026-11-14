import Langlands.Geometry.Building.AffineReflectionGalleryGeometry
import Langlands.Geometry.Building.AffineChamberSimpleCone

/-! # Indivisible affine roots and chamber-simple roots -/

noncomputable section

open Filter Topology

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- An affine root becomes a chamber-simple root or its negative under
pullback by a root-preserving affine automorphism. -/
def IsSimpleRootConjugate (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A)
    (ψ : A →ᵃ[ℝ] ℝ) : Prop :=
  ∃ (e : A ≃ᵃ[ℝ] A), e ∈ rootStabilizer Ψ ∧
    ∃ η ∈ simpleAffineRoots Ψ C,
      ψ.comp (e : A →ᵃ[ℝ] A) = η ∨ ψ.comp (e : A →ᵃ[ℝ] A) = -η

namespace GalleryGeometry

/-- A coroot reflection is conjugate by a product of chamber wall reflections
    to a wall reflection of any prescribed chamber. -/
theorem exists_conjugate_mem_wallReflections
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {x : A} (hx : IsRegular Ψ x) {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) {v : V}
    (hv : IsCoroot Ψ ψ v) :
    ∃ w ∈ Subgroup.closure (wallReflections Ψ x),
      w⁻¹ * affineReflection ψ hv.1 * w ∈ wallReflections Ψ x := by
  classical
  have hsst : affineReflection ψ hv.1 ∈ rootStabilizer Ψ :=
    affineReflection_mem_rootStabilizer hv
  let g : (A →ᵃ[ℝ] ℝ) → (A →ᵃ[ℝ] ℝ) := fun η => η - (η.linear v / 2) • ψ
  have hg : ∀ η p, g η p = η p - η.linear v / 2 * ψ p := fun η p => by
    simp only [g, AffineMap.coe_sub, AffineMap.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  let F : Set (A →ᵃ[ℝ] ℝ) :=
    g '' {η | η ∈ separatingRoots Ψ x (affineReflection ψ hv.1 x) ∧ (g η).linear ≠ 0}
  have hFf : F.Finite :=
    ((finite_separatingRoots hΨ x (affineReflection ψ hv.1 x)).subset
      fun η hη => hη.1).image g
  have hFl : ∀ f ∈ F, f.linear ≠ 0 := by
    rintro _ ⟨η, hη, rfl⟩
    exact hη.2
  obtain ⟨x', hxx', hx'F⟩ := exists_facetRel_forall_ne_zero hΨ hx hFf hFl
  have hx' := hx.of_facetRel hxx'
  have hsxx' : facetRel Ψ (affineReflection ψ hv.1 x) (affineReflection ψ hv.1 x') :=
    (facetRel_apply_iff hsst x x').2 hxx'
  -- `m` is the midpoint of `x'` and its reflection, a generic point of the hyperplane.
  obtain ⟨m, hm⟩ : ∃ m : A, m = (-(ψ x') / 2) • v +ᵥ x' := ⟨_, rfl⟩
  have hgm : ∀ η : A →ᵃ[ℝ] ℝ, η m = g η x' := by
    intro η
    rw [hm, apply_smul_vadd, hg]
    ring
  have hψm : ψ m = 0 := by
    rw [hgm, hg, hv.1]
    ring
  have hmne : ∀ η ∈ Ψ, (¬∃ c : ℝ, η = c • ψ) → η m ≠ 0 := by
    intro η hη hprop hηm
    by_cases hlin : (g η).linear = 0
    · refine hprop ⟨η.linear v / 2, ?_⟩
      have := eq_zero_of_linear_eq_zero hlin (p := x') (by rw [← hgm]; exact hηm)
      exact sub_eq_zero.1 this
    · have hηR : η ∈ separatingRoots Ψ x (affineReflection ψ hv.1 x) := by
        refine ⟨hη, ?_⟩
        have h0 := hgm η
        rw [hηm, hg] at h0
        have h1 : η (affineReflection ψ hv.1 x') = -η x' := by
          rw [affineReflection_apply, AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
          linarith
        have h2 : η x' * η (affineReflection ψ hv.1 x') < 0 := by
          rw [h1]
          have := mul_self_pos.2 (hx' η hη)
          linarith
        exact mul_neg_of_sign_eq (hxx' η hη).symm (hsxx' η hη).symm h2
      exact hx'F (g η) ⟨η, ⟨hηR, hlin⟩, rfl⟩ (by rw [← hgm]; exact hηm)
  -- A regular point near `m`, off the hyperplane of `ψ`.
  obtain ⟨δ, hδ, hδsign⟩ := exists_pos_of_eventually (eventually_sign_smul_vadd hΨ m v)
  have hx''reg : IsRegular Ψ (δ • v +ᵥ m) := by
    intro η hη
    by_cases hprop : ∃ c : ℝ, η = c • ψ
    · obtain ⟨c, rfl⟩ := hprop
      have hc : c ≠ 0 := by
        rintro rfl
        exact hΨ.linear_ne_zero _ hη (by simp)
      have hψx'' : ψ (δ • v +ᵥ m) = δ * 2 := by
        rw [apply_smul_vadd, hψm, hv.1, zero_add]
      show c * ψ (δ • v +ᵥ m) ≠ 0
      rw [hψx'']
      exact mul_ne_zero hc (by positivity)
    · intro h0
      have := hδsign η hη (hmne η hη hprop)
      rw [h0, sign_zero, eq_comm, sign_eq_zero_iff] at this
      exact hmne η hη hprop this
  have hwall : affineReflection ψ hv.1 ∈ wallReflections Ψ (δ • v +ᵥ m) :=
    mem_wallReflections_of_sign_eq hΨ hψ hv hx''reg hψm fun η hη hprop =>
      hδsign η hη (hmne η hη hprop)
  -- Transport the wall to the chamber of `x` along a gallery.
  obtain ⟨w, hw, hwx⟩ := exists_facetRel hΨ hx hx''reg
  have hwall' := mem_wallReflections_of_facetRel ((facetRel_equivalence Ψ).symm hwx) hwall
  have h1 := conj_mem_wallReflections (inv_mem (mem_rootStabilizer_of_mem_closure hw)) hwall'
  rw [inv_inv, show w⁻¹ (w x) = x from w.symm_apply_apply x] at h1
  exact ⟨w, hw, h1⟩

end GalleryGeometry

open GalleryGeometry

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)
include hΨ

/-- Two indivisible affine roots that are positive multiples are equal. -/
theorem eq_of_mem_nonDivisibleRoots_of_eq_smul {ψ η : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ nonDivisibleRoots Ψ) (hη : η ∈ nonDivisibleRoots Ψ) {r : ℝ}
    (hr : 0 < r) (h : η = r • ψ) : η = ψ := by
  obtain ⟨u, hu⟩ := hΨ.exists_isCoroot ψ hψ.1
  have hu' : IsCoroot Ψ η (r⁻¹ • u) := by
    refine ⟨?_, fun ζ hζ => ?_⟩
    · rw [h, AffineMap.smul_linear, LinearMap.smul_apply, map_smul, hu.1, smul_eq_mul,
        smul_eq_mul]
      field_simp
    · have := hu.2 ζ hζ
      convert this using 2
      rw [h, map_smul, smul_eq_mul, smul_smul]
      congr 1
      field_simp
  obtain ⟨n₁, hn₁⟩ := hΨ.coroot_integral η hη.1 ψ hψ.1 u hu
  obtain ⟨n₂, hn₂⟩ := hΨ.coroot_integral ψ hψ.1 η hη.1 _ hu'
  have h1 : (n₁ : ℝ) = 2 * r := by
    rw [← hn₁, h, AffineMap.smul_linear, LinearMap.smul_apply, hu.1, smul_eq_mul]
    ring
  have h2 : (n₂ : ℝ) = 2 * r⁻¹ := by
    rw [← hn₂, map_smul, hu.1, smul_eq_mul]
    ring
  have h12 : n₁ * n₂ = 4 := by
    have : (n₁ : ℝ) * n₂ = 4 := by
      rw [h1, h2]
      field_simp
      ring
    exact_mod_cast this
  have hn₁pos : 0 < n₁ := by
    have : (0 : ℝ) < n₁ := by rw [h1]; positivity
    exact_mod_cast this
  have hn₂pos : 0 < n₂ := by
    have : (0 : ℝ) < n₂ := by rw [h2]; positivity
    exact_mod_cast this
  have hn₁le : n₁ ≤ 4 := by nlinarith
  interval_cases n₁
  · exfalso
    apply hψ.2
    have hr' : r = 1 / 2 := by push_cast at h1; linarith
    have : (2 : ℝ)⁻¹ • ψ = η := by rw [h, hr']; norm_num
    rw [this]
    exact hη.1
  · have hr' : r = 1 := by push_cast at h1; linarith
    rw [h, hr', one_smul]
  · omega
  · exfalso
    apply hη.2
    have hr' : r = 2 := by push_cast at h1; linarith
    rw [h, hr', smul_smul]
    norm_num
    exact hψ.1

/-- Negation preserves indivisibility. -/
theorem neg_mem_nonDivisibleRoots {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ nonDivisibleRoots Ψ) : -ψ ∈ nonDivisibleRoots Ψ := by
  refine ⟨hΨ.neg_mem hψ.1, fun h => hψ.2 ?_⟩
  simpa only [smul_neg, neg_neg] using hΨ.neg_mem h

end IsAffineRootSystemWithRankZero

/-- Pullback by a root-preserving affine map preserves indivisibility. -/
theorem comp_mem_nonDivisibleRoots {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ nonDivisibleRoots Ψ) :
    ψ.comp (e : A →ᵃ[ℝ] A) ∈ nonDivisibleRoots Ψ := by
  refine ⟨(comp_mem_iff he ψ).mpr hψ.1, fun h => hψ.2 ?_⟩
  apply (comp_mem_iff he ((2 : ℝ)⁻¹ • ψ)).mp
  convert h using 1
  ext x
  rfl

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)
include hΨ

/-- Every indivisible affine root is, up to sign and root-preserving pullback,
a simple affine root of a prescribed regular chamber. -/
theorem exists_simple_eq_comp_or_neg {c : A} (hc : IsRegular Ψ c)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ nonDivisibleRoots Ψ) :
    IsSimpleRootConjugate Ψ (facet Ψ c) ψ := by
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot ψ hψ.1
  obtain ⟨w, hw, hwall⟩ := GalleryGeometry.exists_conjugate_mem_wallReflections
    hΨ.isLocallyFiniteReflectionArrangement hc hψ.1 hv
  have hwstab := GalleryGeometry.mem_rootStabilizer_of_mem_closure hw
  have htrans : IsCoroot Ψ (ψ.comp (w : A →ᵃ[ℝ] A)) (w⁻¹.linear v) := by
    simpa only [← AffineEquiv.inv_def, inv_inv] using hv.map (inv_mem hwstab)
  have hwall' : affineReflection (ψ.comp (w : A →ᵃ[ℝ] A)) htrans.1 ∈
      wallReflections Ψ c := by
    have href := conjugate_affineReflection w⁻¹ ψ hv.1
    simp only [← AffineEquiv.inv_def, inv_inv] at href
    rw [← href]
    exact hwall
  obtain ⟨η, hη, r, hprop⟩ :=
    exists_simple_smul_of_mem_wallReflections hΨ hc htrans hwall'
  have hφ := comp_mem_nonDivisibleRoots hwstab hψ
  have hr0 : r ≠ 0 := by
    intro hr
    apply hΨ.linear_ne_zero _ hφ.1
    rw [hprop, hr]
    simp
  refine ⟨w, hwstab, η, hη, ?_⟩
  rcases hr0.lt_or_gt with hr | hr
  · right
    have hn : -(ψ.comp (w : A →ᵃ[ℝ] A)) = η :=
      hΨ.eq_of_mem_nonDivisibleRoots_of_eq_smul hη.2.1
        (hΨ.neg_mem_nonDivisibleRoots hφ) (neg_pos.mpr hr) (by
          rw [hprop, neg_smul])
    exact neg_eq_iff_eq_neg.mp hn
  · left
    exact hΨ.eq_of_mem_nonDivisibleRoots_of_eq_smul hη.2.1 hφ hr hprop

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
