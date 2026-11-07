import Langlands.AlgebraicGeometry.IntegralFibreNeighborhoods

/-! # Compatible affine neighborhoods for integral pinching -/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Langlands.AlgebraicGeometry

/-- Lift a principal open of the intersection with a closed subscheme to a
principal affine open of the ambient affine open. -/
theorem exists_affineOpen_lift_principal
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (t : Γ(Z, i ⁻¹ᵁ U)) :
    ∃ V : X.Opens, IsAffineOpen V ∧ V ≤ U ∧ i ⁻¹ᵁ V = Z.basicOpen t := by
  let : IsAffine U.toScheme := hU
  obtain ⟨s, hs⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine (i ∣_ U)).2
    ((i ⁻¹ᵁ U).topIso.inv t)
  let V : X.Opens := U.ι ''ᵁ U.toScheme.basicOpen s
  refine ⟨V, ((isAffineOpen_top U.toScheme).basicOpen s).image_of_isOpenImmersion U.ι,
    ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · dsimp only [V]
    rw [← image_morphismRestrict_preimage, Scheme.preimage_basicOpen_top, hs,
      Scheme.Opens.ι_image_basicOpen_topIso_inv]

/-- Compatible affine neighborhoods can be chosen inside any prescribed affine
neighborhood of the entire fibre and any affine neighborhood of its image. -/
theorem exists_compatible_affineOpens_of_integral_at
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j] (y : Y)
    (U₀ : X.Opens) (hU₀ : IsAffineOpen U₀)
    (hFU₀ : ∀ z : Z, j z = y → i z ∈ U₀)
    (V₀ : Y.Opens) (hV₀ : IsAffineOpen V₀) (hyV₀ : y ∈ V₀) :
    ∃ U : X.affineOpens, ∃ V : Y.affineOpens,
      y ∈ V.1 ∧ U.1 ≤ U₀ ∧ V.1 ≤ V₀ ∧ i ⁻¹ᵁ U.1 = j ⁻¹ᵁ V.1 := by
  obtain ⟨t, hFt, htV₀⟩ := exists_basicOpen_of_integral_fibre_in_affineOpen
    j y (i ⁻¹ᵁ U₀) (hU₀.preimage i) hFU₀
    (j ⁻¹ᵁ V₀) (fun z hz => by
      change j z ∈ V₀
      rwa [hz])
  obtain ⟨U₁, hU₁, hU₁U₀, hT₁⟩ := exists_affineOpen_lift_principal i U₀ hU₀ t
  have hT₁V₀ : i ⁻¹ᵁ U₁ ≤ j ⁻¹ᵁ V₀ := by
    rw [hT₁]
    exact htV₀
  have hFU₁ : ∀ z : Z, j z = y → i z ∈ U₁ := by
    intro z hz
    exact (show z ∈ i ⁻¹ᵁ U₁ from hT₁ ▸ hFt z hz)
  let W : Y.Opens :=
    ⟨(j '' ((i ⁻¹ᵁ U₁ : Z.Opens) : Set Z)ᶜ)ᶜ,
      (j.isClosedMap _ (i ⁻¹ᵁ U₁).2.isClosed_compl).isOpen_compl⟩
  have hyW : y ∈ W := by
    rintro ⟨z, hz, hzy⟩
    exact hz (hFU₁ z hzy)
  have hWT₁ : j ⁻¹ᵁ W ≤ i ⁻¹ᵁ U₁ := by
    intro z hz
    by_contra hz'
    exact hz ⟨z, hz', rfl⟩
  obtain ⟨s, hsW, hys⟩ := hV₀.exists_basicOpen_le ⟨y, hyW⟩ hyV₀
  have hsT₁ : j ⁻¹ᵁ Y.basicOpen s ≤ i ⁻¹ᵁ U₁ :=
    (j.preimage_mono hsW).trans hWT₁
  obtain ⟨U, hU, hUU₁, hTU⟩ := exists_affineOpen_lift_principal
    i U₁ hU₁ (j.appLE V₀ (i ⁻¹ᵁ U₁) hT₁V₀ s)
  refine ⟨⟨U, hU⟩, ⟨Y.basicOpen s, hV₀.basicOpen s⟩, hys,
    hUU₁.trans hU₁U₀, Y.basicOpen_le s, ?_⟩
  rw [hTU, Scheme.basicOpen_appLE, inf_eq_right.mpr hsT₁]

/-- The fibre-affine-neighborhood hypothesis supplies compatible affine opens
around every point on the integral side. -/
theorem exists_compatible_affineOpens_of_integral
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) (y : Y) :
    ∃ U : X.affineOpens, ∃ V : Y.affineOpens,
      y ∈ V.1 ∧ i ⁻¹ᵁ U.1 = j ⁻¹ᵁ V.1 := by
  obtain ⟨U₀, hU₀, hFU₀⟩ := hF y
  obtain ⟨V₀, hV₀, hyV₀, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, V, hyV, _, _, hUV⟩ :=
    exists_compatible_affineOpens_of_integral_at i j y U₀ hU₀ hFU₀ V₀ hV₀ hyV₀
  exact ⟨U, V, hyV, hUV⟩

/-- Choose a compatible affine pair around a point on the integral side. -/
noncomputable def integralCompatibleAffineNeighborhood
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegralHom j]
    (hF : ∀ y : Y, ∃ U : X.Opens,
      IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) (y : Y) :
    {p : X.affineOpens × Y.affineOpens //
      y ∈ p.2.1 ∧ i ⁻¹ᵁ p.1.1 = j ⁻¹ᵁ p.2.1} :=
  let h := exists_compatible_affineOpens_of_integral i j hF y
  let U := Classical.choose h
  let hU := Classical.choose_spec h
  let V := Classical.choose hU
  ⟨(U, V), Classical.choose_spec hU⟩

end Langlands.AlgebraicGeometry
