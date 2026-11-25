import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearComposition

/-! # Transitivity of the test relations and the subgroups `G_τ(X)` -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Transitivity

variable {T B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Two strong maps near a common third one are near each other, by the strong triangle
inequality of the points of the spectrum. -/
theorem StrongNear.of_common {τ : TestTriple B} {x₀ x₁ x₂ : T ⟶ B}
    (h₁ : StrongNear τ x₀ x₁) (h₂ : StrongNear τ x₀ x₂) : StrongNear τ x₁ x₂ := by
  obtain ⟨hpre₁, hcov₁, hb₁⟩ := h₁
  obtain ⟨hpre₂, hcov₂, hb₂⟩ := h₂
  refine ⟨hpre₁.symm.trans hpre₂, fun y hy => ?_, fun i hi p => ?_⟩
  · have hy0 : y ∈ x₀.baseMap ⁻¹' τ.locus := by rw [hpre₁]; exact hy
    obtain ⟨i₁, hi₁, hyi₁⟩ := hcov₁ y hy0
    obtain ⟨i₂, hi₂, hyi₂⟩ := hcov₂ y hy0
    obtain ⟨l, hyl, hl⟩ := exists_chart_mem_subset_inter T i₁ i₂ hyi₁ hyi₂
    exact ⟨l, ⟨(Set.image_mono (hl.trans Set.inter_subset_left)).trans hi₁.2,
      (Set.image_mono (hl.trans Set.inter_subset_right)).trans hi₂.2⟩, hyl⟩
  · have h0 : x₀.baseMap '' Set.range (T.presentation.atlas.chart i) ⊆ τ.locus := by
      rintro _ ⟨z, hz, rfl⟩
      have hz1 : z ∈ x₁.baseMap ⁻¹' τ.locus := hi.1 ⟨z, hz, rfl⟩
      rw [← hpre₁] at hz1
      exact hz1
    have e₁ := hb₁ i ⟨h0, hi.1⟩ p
    have e₂ := hb₂ i ⟨h0, hi.2⟩ p
    have hsplit : x₁.pullback i τ.domain hi.1 τ.function - x₂.pullback i τ.domain hi.2 τ.function =
        -(x₀.pullback i τ.domain h0 τ.function - x₁.pullback i τ.domain hi.1 τ.function) +
          (x₀.pullback i τ.domain h0 τ.function - x₂.pullback i τ.domain hi.2 τ.function) := by
      abel
    rw [hsplit]
    refine ((BanachSpectrum.isNonarchimedean (K := K) p) _ _).trans (max_le ?_ e₂)
    rw [map_neg_eq_map]
    exact e₁

variable {X Y : LocalizedCategory.{u, v, w} (K := K)} {τ : TestTriple (presentationOf X)}

/-- **Transitivity of the test relation** in the localized category. -/
theorem IsNear.trans {φ ψ χ : Y ⟶ X} (h₁ : IsNear τ φ ψ) (h₂ : IsNear τ ψ χ) :
    IsNear τ φ χ := by
  obtain ⟨S, s, hs, x₀, x₁, x₂, -, h1, h2, hE⟩ := exists_strongNear_numerators {τ} ψ φ χ
    (fun σ hσ => by rw [Finset.mem_singleton.1 hσ]; exact h₁.symm)
    (fun σ hσ => by rw [Finset.mem_singleton.1 hσ]; exact h₂)
  have h := hE τ (Finset.mem_singleton_self τ)
  exact (isNear_iff_numerators τ φ χ).2 ⟨S, s, hs, x₁, x₂, h1, h2, h.1.of_common h.2⟩

/-- Endomorphisms near the identity are closed under composition. -/
theorem IsNear.comp_of_isNear_id {τ : TestTriple (presentationOf Y)} {φ ψ : Y ⟶ Y}
    (hφ : IsNear τ φ (𝟙 Y)) (hψ : IsNear τ ψ (𝟙 Y)) : IsNear τ (φ ≫ ψ) (𝟙 Y) := by
  have h := hψ.precomp φ
  rw [Category.comp_id] at h
  exact h.trans hφ

/-- Berkovich's set `G_τ(X)` of automorphisms near the identity is a subgroup. -/
def nearIdentitySubgroup (τ : TestTriple (presentationOf X)) : Subgroup (Aut X) where
  carrier := nearIdentity τ
  one_mem' := one_mem_nearIdentity τ
  mul_mem' {σ σ'} hσ hσ' := by
    change IsNear τ (σ'.asIso.hom ≫ σ.asIso.hom) (𝟙 X)
    exact IsNear.comp_of_isNear_id hσ' hσ
  inv_mem' {σ} hσ := by
    change IsNear τ σ.asIso.inv (𝟙 X)
    have h := IsNear.precomp (τ := τ) hσ σ.asIso.inv
    have h2 : σ.asIso.inv ≫ σ.asIso.hom = 𝟙 X := σ.asIso.inv_hom_id
    rw [h2, Category.comp_id] at h
    exact h.symm

theorem mem_nearIdentitySubgroup (τ : TestTriple (presentationOf X)) (σ : Aut X) :
    σ ∈ nearIdentitySubgroup τ ↔ σ ∈ nearIdentity τ :=
  Iff.rfl

end Transitivity

end Langlands.Analytic.SaturatedAtlasPresentation
