import Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGeneric

/-! # Fibrewise density of a domain and its translates, by generic points -/

open Topology

namespace Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction

variable {T T' B : Type*} [TopologicalSpace T] [TopologicalSpace T']

/-- Under an open embedding `e`, a point is generic in its fibre under `p ∘ e` exactly when its
image is generic in its fibre under `p`. -/
theorem isFibreGeneric_comp_iff {e : T' → T} (he : IsOpenEmbedding e) (p : T → B) (u : T') :
    IsFibreGeneric (p ∘ e) u ↔ IsFibreGeneric p (e u) := by
  constructor
  · intro h y' hy' hpy'
    obtain ⟨u', rfl⟩ : y' ∈ Set.range e := hy'.mem_open he.isOpen_range ⟨u, rfl⟩
    rw [h u' (he.isInducing.specializes_iff.mp hy') hpy']
  · intro h u' hu' hpu'
    exact he.injective (h (e u') (hu'.map he.continuous) hpu')

variable {Y X D : Type*} [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace D]

/-- The six fibrewise density conditions for a law `m` with domain `ι : D → Y` and universal
translations `Φ, Ψ : D → Y`, reduced to generic points of fibres. Here `Y` plays the role of
`X ×_S X` with projections `p₁, p₂`, `F` that of the generic points of the fibres of `X` over
`S`, and `X'` that of an open subset containing `F` such that the images of `ι`, `Φ` and `Ψ`
contain the generic points of the fibres of `p₁` and `p₂` over the points of `X'`. -/
theorem translation_density (p₁ p₂ : Y → X) (hp₁ : Continuous p₁) (hp₂ : Continuous p₂)
    (ι Φ Ψ : D → Y) (m : D → X) (hι : IsOpenEmbedding ι) (hΦ : IsOpenEmbedding Φ)
    (hΨ : IsOpenEmbedding Ψ) (hΦ₁ : p₁ ∘ Φ = p₁ ∘ ι) (hΦ₂ : p₂ ∘ Φ = m)
    (hΨ₁ : p₁ ∘ Ψ = m) (hΨ₂ : p₂ ∘ Ψ = p₂ ∘ ι) (F X' : Set X) (hX' : IsOpen X')
    (hFX' : F ⊆ X')
    (hex₁ : ∀ y, ∃ y₀, IsFibreGeneric p₁ y₀ ∧ p₁ y₀ = p₁ y ∧ y₀ ⤳ y)
    (hex₂ : ∀ y, ∃ y₀, IsFibreGeneric p₂ y₀ ∧ p₂ y₀ = p₂ y ∧ y₀ ⤳ y)
    (ha₁ : ∀ y, IsFibreGeneric p₁ y → p₂ y ∈ F) (ha₂ : ∀ y, IsFibreGeneric p₂ y → p₁ y ∈ F)
    (hG₁ : ∀ y, IsFibreGeneric p₁ y → p₁ y ∈ X' →
      y ∈ Set.range ι ∧ y ∈ Set.range Φ ∧ y ∈ Set.range Ψ)
    (hG₂ : ∀ y, IsFibreGeneric p₂ y → p₂ y ∈ X' →
      y ∈ Set.range ι ∧ y ∈ Set.range Φ ∧ y ∈ Set.range Ψ) :
    let U' : Set Y := {y | p₁ y ∈ X' ∧ p₂ y ∈ X' ∧ ∃ u, ι u = y ∧ m u ∈ X'}
    let Dense' : (Y → X) → Set Y → Prop := fun q W =>
      ∀ y, p₁ y ∈ X' → p₂ y ∈ X' → ∃ y' ∈ W, q y' = q y ∧ y' ⤳ y
    Dense' p₁ U' ∧ Dense' p₂ U' ∧ Dense' p₁ (Φ '' (ι ⁻¹' U')) ∧ Dense' p₂ (Φ '' (ι ⁻¹' U')) ∧
      Dense' p₁ (Ψ '' (ι ⁻¹' U')) ∧ Dense' p₂ (Ψ '' (ι ⁻¹' U')) := by
  intro U' Dense'
  -- Reduction to generic points.
  have red (q : Y → X) (hex : ∀ y, ∃ y₀, IsFibreGeneric q y₀ ∧ q y₀ = q y ∧ y₀ ⤳ y)
      (W : Set Y) (hW : ∀ y, IsFibreGeneric q y → p₁ y ∈ X' → p₂ y ∈ X' → y ∈ W) :
      Dense' q W := by
    intro y h₁ h₂
    obtain ⟨y₀, hgen, hq, hy₀⟩ := hex y
    exact ⟨y₀, hW y₀ hgen ((hy₀.map hp₁).mem_open hX' h₁) ((hy₀.map hp₂).mem_open hX' h₂),
      hq, hy₀⟩
  -- Transfer of generic points along the embeddings.
  have tΦ₁ (u : D) : IsFibreGeneric p₁ (Φ u) ↔ IsFibreGeneric p₁ (ι u) := by
    rw [← isFibreGeneric_comp_iff hΦ, ← isFibreGeneric_comp_iff hι, hΦ₁]
  have tΨ₂ (u : D) : IsFibreGeneric p₂ (Ψ u) ↔ IsFibreGeneric p₂ (ι u) := by
    rw [← isFibreGeneric_comp_iff hΨ, ← isFibreGeneric_comp_iff hι, hΨ₂]
  have tΦΨ (u : D) : IsFibreGeneric p₂ (Φ u) ↔ IsFibreGeneric p₁ (Ψ u) := by
    rw [← isFibreGeneric_comp_iff hΦ, ← isFibreGeneric_comp_iff hΨ, hΦ₂, hΨ₁]
  have eΦ₁ (u : D) : p₁ (Φ u) = p₁ (ι u) := congrFun hΦ₁ u
  have eΦ₂ (u : D) : p₂ (Φ u) = m u := congrFun hΦ₂ u
  have eΨ₁ (u : D) : p₁ (Ψ u) = m u := congrFun hΨ₁ u
  have eΨ₂ (u : D) : p₂ (Ψ u) = p₂ (ι u) := congrFun hΨ₂ u
  have memU (u : D) (h₁ : p₁ (ι u) ∈ X') (h₂ : p₂ (ι u) ∈ X') (h₃ : m u ∈ X') : ι u ∈ U' :=
    ⟨h₁, h₂, u, rfl, h₃⟩
  refine ⟨red p₁ hex₁ _ ?_, red p₂ hex₂ _ ?_, red p₁ hex₁ _ ?_, red p₂ hex₂ _ ?_,
    red p₁ hex₁ _ ?_, red p₂ hex₂ _ ?_⟩
  · intro y hy h₁ h₂
    obtain ⟨⟨u, rfl⟩, -, -⟩ := hG₁ y hy h₁
    exact memU u h₁ h₂ (eΦ₂ u ▸ hFX' (ha₁ _ ((tΦ₁ u).mpr hy)))
  · intro y hy h₁ h₂
    obtain ⟨⟨u, rfl⟩, -, -⟩ := hG₂ y hy h₂
    exact memU u h₁ h₂ (eΨ₁ u ▸ hFX' (ha₂ _ ((tΨ₂ u).mpr hy)))
  · intro y hy h₁ h₂
    obtain ⟨-, ⟨u, rfl⟩, -⟩ := hG₁ y hy h₁
    have hgu := (tΦ₁ u).mp hy
    exact ⟨u, memU u (eΦ₁ u ▸ h₁) (hFX' (ha₁ _ hgu)) (eΦ₂ u ▸ h₂), rfl⟩
  · intro y hy h₁ h₂
    obtain ⟨-, ⟨u, rfl⟩, -⟩ := hG₂ y hy h₂
    have hgu := (tΦΨ u).mp hy
    exact ⟨u, memU u (eΦ₁ u ▸ h₁) (eΨ₂ u ▸ hFX' (ha₁ _ hgu)) (eΦ₂ u ▸ h₂), rfl⟩
  · intro y hy h₁ h₂
    obtain ⟨-, -, ⟨u, rfl⟩⟩ := hG₁ y hy h₁
    have hgu := (tΦΨ u).mpr hy
    exact ⟨u, memU u (eΦ₁ u ▸ hFX' (ha₂ _ hgu)) (eΨ₂ u ▸ h₂) (eΨ₁ u ▸ h₁), rfl⟩
  · intro y hy h₁ h₂
    obtain ⟨-, -, ⟨u, rfl⟩⟩ := hG₂ y hy h₂
    have hgu := (tΨ₂ u).mp hy
    exact ⟨u, memU u (hFX' (ha₂ _ hgu)) (eΨ₂ u ▸ h₂) (eΨ₁ u ▸ h₁), rfl⟩

end Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction
