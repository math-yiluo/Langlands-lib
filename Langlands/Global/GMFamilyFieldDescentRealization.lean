import Langlands.Global.GMFamilyFieldDescentTransport
import Langlands.LinearAlgebra.GMFamilyFieldDescentMetric

/-! # The field-descent formula for linear-algebra descent data -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Module Submodule

namespace Langlands.GMFamily

namespace FieldDescentData

open RootRestriction

variable {V₁ V : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
  [AddCommGroup V] [Module ℝ V]
variable (D : FieldDescentData V₁ V)

/-- The Euclidean space of coordinates on `V₁`. -/
abbrev E : Type := EuclideanSpace ℝ (Fin (finrank ℝ V₁))

/-- The fine roots in the coordinates on `V₁`: the nonzero restrictions of the roots. -/
abbrev R : Finset (E (V₁ := V₁)) := restrictRoots D.φ D.R₀

/-- The coarse subspace in the coordinates on `V₁`. -/
abbrev b : Submodule ℝ (E (V₁ := V₁)) := D.B.map D.e₁.toLinearMap

theorem inner_res_rv (γ : Module.Dual ℝ V) (x : V₁) :
    ⟪res D.φ (D.rv γ), D.e₁ x⟫ = γ (D.κ x) := by
  rw [inner_res, φ_e₁, inner_rv]

/-- The restriction of the vector of a root is the vector of its restriction. -/
theorem res_rv (γ : Module.Dual ℝ V) :
    res D.φ (D.rv γ) = (InnerProductSpace.toDual ℝ (E (V₁ := V₁))).symm
      (LinearMap.toContinuousLinearMap ((γ ∘ₗ D.κ) ∘ₗ D.e₁.symm.toLinearMap)) := by
  apply ext_inner_right ℝ
  intro x
  rw [← D.e₁.apply_symm_apply x, inner_res_rv, InnerProductSpace.toDual_symm_apply]
  simp

theorem mem_R {α : E (V₁ := V₁)} :
    α ∈ D.R ↔ α ≠ 0 ∧ ∃ γ ∈ D.roots, res D.φ (D.rv γ) = α := by
  rw [mem_restrictRoots]
  simp only [R₀, Finset.mem_image, exists_exists_and_eq_and]

/-- The central directions in the coordinates on `V₁`. -/
theorem e₁_mem_centralSpace {w : V₁} : D.e₁ w ∈ centralSpace D.R ↔ w ∈ D.Z₁ := by
  rw [centralSpace, mem_iInf_orthogonal_iff, mem_Z₁]
  constructor
  · intro H γ hγ
    by_cases h0 : res D.φ (D.rv γ) = 0
    · rw [← inner_res_rv, h0, inner_zero_left]
    · rw [← inner_res_rv]
      exact H _ ((D.mem_R).mpr ⟨h0, γ, hγ, rfl⟩)
  · intro H α hα
    obtain ⟨-, γ, hγ, rfl⟩ := (D.mem_R).mp hα
    rw [inner_res_rv]
    exact H γ hγ

/-- **The image of the fine coordinates is a Levi flat.** -/
theorem isLeviSpace : IsLeviSpace D.R₀ (mapSub (φ := D.φ) ⊤) := by
  let I := D.roots.filter (fun γ => γ.comp D.κ ≠ 0)
  have hex : ∀ i : I, ∃ y : V₁, ((i : Module.Dual ℝ V).comp D.κ) y ≠ 0 := by
    intro i
    by_contra hn
    push Not at hn
    exact (Finset.mem_filter.mp i.prop).2 (LinearMap.ext hn)
  obtain ⟨y₀, hy₀⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun i : I => (i : Module.Dual ℝ V).comp D.κ) hex
  have hgen : ∀ γ ∈ D.roots, γ (D.κ y₀) = 0 → γ.comp D.κ = 0 := by
    intro γ hγ h0
    by_contra hne
    exact hy₀ ⟨γ, Finset.mem_filter.mpr ⟨hγ, hne⟩⟩ h0
  refine ⟨D.eT (D.κ y₀), ?_⟩
  ext x
  rw [mem_leviSpaceOf_iff]
  constructor
  · rintro ⟨u, -, rfl⟩ r hr _
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hr
    have hu : D.φ u = D.eT (D.κ (D.e₁.symm u)) := by
      rw [← φ_e₁, LinearEquiv.apply_symm_apply]
    change ⟪D.rv γ, D.φ u⟫ = 0
    rw [hu, inner_rv]
    rename_i h
    rw [inner_rv] at h
    exact LinearMap.congr_fun (hgen γ hγ h) _
  · intro H
    have hmem : D.eT.symm x ∈ LinearMap.range D.κ := by
      rw [D.range_eq]
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro γ hγ
      obtain ⟨hγR, hγ0⟩ := Finset.mem_filter.mp hγ
      have h := H (D.rv γ) (Finset.mem_image_of_mem _ hγR) (by
        rw [inner_rv]
        exact LinearMap.congr_fun hγ0 y₀)
      rwa [← D.eT.apply_symm_apply x, inner_rv] at h
    obtain ⟨w, hw⟩ := hmem
    refine ⟨D.e₁ w, Submodule.mem_top, ?_⟩
    change D.φ (D.e₁ w) = x
    rw [φ_e₁, hw, LinearEquiv.apply_symm_apply]

/-- **The central projection preserves the coarse subspace.** -/
theorem starProjection_mem_b {x : E (V₁ := V₁)} (hx : x ∈ D.b) :
    (centralSpace D.R).starProjection x ∈ D.b := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hp : (centralSpace D.R).starProjection (D.e₁ u) = D.e₁ (D.pB u) := by
    apply eq_starProjection_of_mem_of_inner_eq_zero
    · exact (D.e₁_mem_centralSpace).mpr (D.pB_mem u).1
    · intro w hw
      rw [← D.e₁.apply_symm_apply w] at hw ⊢
      rw [← map_sub, inner_e₁]
      exact D.inner_F_central hu ((D.e₁_mem_centralSpace).mp hw)
  change (centralSpace D.R).starProjection (D.e₁ u) ∈ D.b
  rw [hp]
  exact ⟨D.pB u, (D.pB_mem u).2, rfl⟩

theorem inner_e₁_B_K {x y : V₁} (hx : x ∈ D.B) (hy : y ∈ D.K) : ⟪D.e₁ x, D.e₁ y⟫ = 0 := by
  rw [inner_e₁]
  exact D.inner_F_B_K hx hy

/-- A vector orthogonal to the image of `K` lies in the coarse subspace. -/
theorem mem_b_of_orthogonal {v : E (V₁ := V₁)} (hv : ∀ y ∈ D.K, ⟪v, D.e₁ y⟫ = 0) : v ∈ D.b := by
  obtain ⟨u, rfl⟩ := D.e₁.surjective v
  have hB : D.πB u ∈ D.B := Submodule.projection_apply_mem D.isCompl u
  have hK : D.πK u ∈ D.K := Submodule.projection_apply_mem D.isCompl.symm u
  have h1 := hv _ hK
  have hu : D.e₁ u = D.e₁ (D.πB u) + D.e₁ (D.πK u) := by rw [← map_add, D.πB_add_πK]
  rw [hu, inner_add_left, D.inner_e₁_B_K hB hK, zero_add] at h1
  have h0 : D.e₁ (D.πK u) = 0 := inner_self_eq_zero.mp h1
  refine ⟨D.πB u, hB, ?_⟩
  change D.e₁ (D.πB u) = D.e₁ u
  rw [hu, h0, add_zero]

theorem restrictedRoot_b_eq_iff {z z' : E (V₁ := V₁)} :
    restrictedRoot D.b z = restrictedRoot D.b z' ↔ ∀ u ∈ D.B, ⟪z, D.e₁ u⟫ = ⟪z', D.e₁ u⟫ := by
  rw [← sub_eq_zero, restrictedRoot, restrictedRoot, ← map_sub,
    orthogonalProjectionOnto_eq_zero_iff, Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    have := h (D.e₁ u) ⟨u, hu, rfl⟩
    rw [inner_sub_right, sub_eq_zero, real_inner_comm, real_inner_comm z'] at this
    exact this
  · rintro h _ ⟨u, hu, rfl⟩
    change ⟪D.e₁ u, z - z'⟫ = 0
    rw [inner_sub_right, sub_eq_zero, real_inner_comm, real_inner_comm z']
    exact h u hu

/-- The weights of the roots in the Euclidean model. -/
def m₀ (r : D.E₀) : ℝ := ∑ γ ∈ D.roots.filter (fun γ => D.rv γ = r), D.mult γ

theorem m₀_rv {γ : Module.Dual ℝ V} (hγ : γ ∈ D.roots) : D.m₀ (D.rv γ) = D.mult γ := by
  have h : D.roots.filter (fun δ => D.rv δ = D.rv γ) = {γ} := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact D.rv_injective h
    · rintro rfl
      exact ⟨hγ, rfl⟩
  rw [m₀, h, Finset.sum_singleton]

theorem m₀_pos {r : D.E₀} (hr : r ∈ D.R₀) : 0 < D.m₀ r := by
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hr
  rw [D.m₀_rv hγ]
  exact D.mult_pos γ hγ

/-- **The coarse subspace is special.** -/
theorem special_sums (β : D.b) (hβ : β ≠ 0) :
    (∑ α ∈ D.R.filter (fun α => restrictedRoot D.b α = β),
      (∑ r ∈ D.R₀.filter (fun r => res D.φ r = α), D.m₀ r) • α) ∈ D.b := by
  apply D.mem_b_of_orthogonal
  intro y hy
  let s := D.R₀.filter (fun r => restrictedRoot D.b (res D.φ r) = β)
  let t := D.R.filter (fun α => restrictedRoot D.b α = β)
  have hmaps : ∀ r ∈ s, res D.φ r ∈ t := by
    intro r hr
    obtain ⟨hrR, hrβ⟩ := Finset.mem_filter.mp hr
    refine Finset.mem_filter.mpr ⟨?_, hrβ⟩
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hrR
    refine (D.mem_R).mpr ⟨fun h0 => hβ ?_, γ, hγ, rfl⟩
    rw [← hrβ, h0]
    exact Subtype.ext (by simp [restrictedRoot])
  have h1 : ⟪∑ α ∈ t, (∑ r ∈ D.R₀.filter (fun r => res D.φ r = α), D.m₀ r) • α, D.e₁ y⟫ =
      ∑ r ∈ s, D.m₀ r * ⟪res D.φ r, D.e₁ y⟫ := by
    rw [sum_inner, ← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro α hα
    rw [real_inner_smul_left, Finset.sum_mul]
    have hst : s.filter (fun r => res D.φ r = α) = D.R₀.filter (fun r => res D.φ r = α) := by
      ext r
      simp only [Finset.mem_filter, s]
      constructor
      · rintro ⟨⟨h, -⟩, he⟩
        exact ⟨h, he⟩
      · rintro ⟨h, he⟩
        exact ⟨⟨h, he ▸ (Finset.mem_filter.mp hα).2⟩, he⟩
    rw [hst]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(Finset.mem_filter.mp hr).2]
  have h2 : ∑ r ∈ s, D.m₀ r * ⟪res D.φ r, D.e₁ y⟫ =
      ∑ γ ∈ D.roots.filter (fun γ => restrictedRoot D.b (res D.φ (D.rv γ)) = β),
        D.mult γ * γ (D.κ y) := by
    have hs : s = (D.roots.filter
        (fun γ => restrictedRoot D.b (res D.φ (D.rv γ)) = β)).image D.rv := by
      simp only [s, R₀, Finset.filter_image]
    rw [hs, Finset.sum_image (fun γ _ δ _ h => D.rv_injective h)]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [D.m₀_rv (Finset.mem_filter.mp hγ).1, inner_res_rv]
  rw [h1, h2]
  by_cases hne : (D.roots.filter (fun γ => restrictedRoot D.b (res D.φ (D.rv γ)) = β)).Nonempty
  · obtain ⟨γ₀, hγ₀⟩ := hne
    obtain ⟨hγ₀R, hγ₀β⟩ := Finset.mem_filter.mp hγ₀
    have hfib : D.roots.filter (fun γ => restrictedRoot D.b (res D.φ (D.rv γ)) = β) =
        D.roots.filter (fun δ => (δ.comp D.κ).domRestrict D.B =
          (γ₀.comp D.κ).domRestrict D.B) := by
      apply Finset.filter_congr
      intro δ _
      rw [← hγ₀β, D.restrictedRoot_b_eq_iff]
      constructor
      · intro h
        ext ⟨u, hu⟩
        have := h u hu
        rw [inner_res_rv, inner_res_rv] at this
        simpa using this
      · intro h u hu
        rw [inner_res_rv, inner_res_rv]
        simpa using LinearMap.congr_fun h ⟨u, hu⟩
    have hβ₀ : (γ₀.comp D.κ).domRestrict D.B ≠ 0 := by
      intro h0
      apply hβ
      rw [← hγ₀β]
      apply Subtype.ext
      have hz : restrictedRoot D.b (res D.φ (D.rv γ₀)) = restrictedRoot D.b 0 := by
        rw [D.restrictedRoot_b_eq_iff]
        intro u hu
        rw [inner_res_rv, inner_zero_left]
        simpa using LinearMap.congr_fun h0 ⟨u, hu⟩
      rw [hz]
      simp [restrictedRoot]
    rw [hfib]
    exact D.special γ₀ hγ₀R hβ₀ y hy
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]

/-- **The field-descent formula for linear-algebra descent data.** -/
theorem hasFieldDescentFormula : HasFieldDescentFormula D.R D.b :=
  hasFieldDescentFormula_of_restrictRoots D.isRootSet_R₀ D.isLeviSpace
    (fun _ hx => D.starProjection_mem_b hx) (fun _ hr => D.m₀_pos hr)
    (fun β hβ => by convert D.special_sums β hβ)

end FieldDescentData

end Langlands.GMFamily
