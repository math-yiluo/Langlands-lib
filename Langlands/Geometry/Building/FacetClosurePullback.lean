import Langlands.Geometry.Building.AffineRootSystem
import Mathlib.Basic.Sign.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-! # Closed facets detected by affine segments and facet pullback -/

noncomputable section

open Filter Topology

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- The segment from a point of a closed facet towards its defining point
lies in the open facet, except possibly at its initial endpoint. -/
theorem lineMap_mem_facet_of_mem_facetClosure
    {Ψ : Set (P →ᵃ[ℝ] ℝ)} {p q : P} (hq : q ∈ facetClosure Ψ p)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    AffineMap.lineMap q p t ∈ facet Ψ p := by
  intro ψ hψ
  have hval : ψ (AffineMap.lineMap q p t) = (1 - t) * ψ q + t * ψ p := by
    simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    ring
  rw [hval]
  rcases hq ψ hψ with h0 | hs
  · have hq0 : ψ q = 0 := sign_eq_zero_iff.1 h0
    rw [hq0, mul_zero, zero_add, sign_mul, sign_pos ht0, one_mul]
  · have h1t : 0 ≤ 1 - t := by linarith
    rcases lt_trichotomy (ψ p) 0 with hp | hp | hp
    · have hqn : ψ q < 0 := by
        rw [sign_neg hp] at hs
        exact sign_eq_neg_one_iff.1 hs
      rw [sign_neg hp, sign_neg (by nlinarith)]
    · rw [hp] at hs ⊢
      rw [sign_zero] at hs
      rw [sign_eq_zero_iff.1 hs]
      simp
    · have hqp : 0 < ψ q := by
        rw [sign_pos hp] at hs
        exact sign_eq_one_iff.1 hs
      rw [sign_pos hp, sign_pos (by nlinarith)]

/-- The closed-facet sign conditions are equivalent to membership of every
positive point of the segment in the open facet. No topology on `P` is needed. -/
theorem mem_facetClosure_iff_lineMap_mem_facet
    (Ψ : Set (P →ᵃ[ℝ] ℝ)) (p q : P) :
    q ∈ facetClosure Ψ p ↔
      ∀ t : ℝ, 0 < t → t ≤ 1 → AffineMap.lineMap q p t ∈ facet Ψ p := by
  refine ⟨fun hq _ ht0 ht1 => lineMap_mem_facet_of_mem_facetClosure hq ht0 ht1, ?_⟩
  intro h ψ hψ
  have hsign : ∀ t : ℝ, 0 < t → t ≤ 1 →
      SignType.sign (ψ p) = SignType.sign ((1 - t) * ψ q + t * ψ p) := by
    intro t ht0 ht1
    have hval : ψ (AffineMap.lineMap q p t) = (1 - t) * ψ q + t * ψ p := by
      simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
      ring
    simpa only [hval] using h t ht0 ht1 ψ hψ
  have hlim :
      Tendsto (fun t : ℝ => (1 - t) * ψ q + t * ψ p) (𝓝[>] 0) (𝓝 (ψ q)) := by
    have hc : Continuous (fun t : ℝ => (1 - t) * ψ q + t * ψ p) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  rcases lt_trichotomy (ψ p) 0 with hp | hp | hp
  · have hqle : ψ q ≤ 0 := by
      apply le_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      have hs := hsign t ht.1 ht.2.le
      rw [sign_neg hp, eq_comm, sign_eq_neg_one_iff] at hs
      exact hs.le
    rcases lt_or_eq_of_le hqle with hqn | hq0
    · exact Or.inr (by rw [sign_neg hqn, sign_neg hp])
    · exact Or.inl (by rw [hq0, sign_zero])
  · have hs := hsign (1 / 2) (by norm_num) (by norm_num)
    rw [hp, sign_zero, eq_comm, sign_eq_zero_iff] at hs
    exact Or.inl (sign_eq_zero_iff.mpr (by linarith))
  · have hqge : 0 ≤ ψ q := by
      apply ge_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      have hs := hsign t ht.1 ht.2.le
      rw [sign_pos hp, eq_comm, sign_eq_one_iff] at hs
      exact hs.le
    rcases eq_or_lt_of_le hqge with hq0 | hqp
    · exact Or.inl (by rw [← hq0, sign_zero])
    · exact Or.inr (by rw [sign_pos hqp, sign_pos hp])

variable {W Q : Type*} [AddCommGroup W] [Module ℝ W] [AddTorsor W Q]

/-- Exact pullback of all open facets by an affine map implies exact pullback
of their combinatorial closures, without injectivity or arrangement axioms. -/
theorem preimage_facetClosure_of_preimage_facet
    (a : P →ᵃ[ℝ] Q) (Ψ : Set (P →ᵃ[ℝ] ℝ)) (Ω : Set (Q →ᵃ[ℝ] ℝ))
    (hfacet : ∀ p : P, a ⁻¹' facet Ω (a p) = facet Ψ p) (p : P) :
    a ⁻¹' facetClosure Ω (a p) = facetClosure Ψ p := by
  ext q
  change a q ∈ facetClosure Ω (a p) ↔ q ∈ facetClosure Ψ p
  rw [mem_facetClosure_iff_lineMap_mem_facet, mem_facetClosure_iff_lineMap_mem_facet]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  rw [← a.apply_lineMap]
  exact Set.ext_iff.mp (hfacet p) _

end Langlands.Geometry.Building.AffineRootSystem
