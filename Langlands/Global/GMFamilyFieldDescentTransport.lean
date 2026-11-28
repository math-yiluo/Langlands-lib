import Langlands.Global.GMFamilyFieldDescentRoots
import Langlands.LinearAlgebra.GMFamilyRootRestriction

/-! # Transport of the field-descent formula along an isometric embedding -/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open Classical Submodule

namespace Langlands.GMFamily

namespace RootRestriction

variable {E E₀ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {φ : E →ₗᵢ[ℝ] E₀} {R₀ : Finset E₀}

theorem up_mono {S S' : Finset E} (h : S ⊆ S') : up φ R₀ S ⊆ up φ R₀ S' := fun _ hγ =>
  mem_up.mpr ⟨(mem_up.mp hγ).1, h (mem_up.mp hγ).2⟩

/-- Families agreeing on the chambers are families together. -/
theorem isFamily_congr {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {R : Finset F} {a : Submodule ℝ F}
    {c c' : Finset F → StrongDual ℝ a → ℂ} (h : ∀ S ∈ parabolics R a, c S = c' S) :
    IsFamily R a c ↔ IsFamily R a c' := by
  unfold IsFamily
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun S hS => h S hS ▸ h1 S hS, fun S hS S' hS' v hadj Λ hΛ => ?_⟩
    rw [← h S hS, ← h S' hS']
    exact h2 S hS S' hS' v hadj Λ hΛ
  · rintro ⟨h1, h2⟩
    refine ⟨fun S hS => (h S hS).symm ▸ h1 S hS, fun S hS S' hS' v hadj Λ hΛ => ?_⟩
    rw [h S hS, h S' hS']
    exact h2 S hS S' hS' v hadj Λ hΛ

theorem cM_congr {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {R : Finset F} {a : Submodule ℝ F}
    {c c' : Finset F → StrongDual ℝ a → ℂ} (h : ∀ S ∈ parabolics R a, c S = c' S)
    (Λ : StrongDual ℝ a) : cM R a c Λ = cM R a c' Λ := by
  unfold cM
  exact Finset.sum_congr rfl fun S hS => by rw [h S hS]

/-- The central part of a subspace and of its image correspond. -/
theorem mapSub_coarseCenter (b : Submodule ℝ E) :
    mapSub (φ := φ) (coarseCenter (restrictRoots φ R₀) b) = coarseCenter R₀ (mapSub (φ := φ) b) :=
  (mapSub_inf_iInf b R₀).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem coarseCenter_le_of_mem_leviSpaces {R : Finset E} {V b L : Submodule ℝ E} (hb : b ≤ V)
    (hL : L ∈ leviSpaces R V) : coarseCenter R b ≤ L := by
  obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hL
  refine le_inf (inf_le_left.trans hb) (le_iInf₂ fun α hα => ?_)
  exact inf_le_right.trans (iInf₂_le α (Finset.mem_filter.mp hα).1)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₀] in
theorem le_of_mem_leviSpaces' {R : Finset E} {V L : Submodule ℝ E} (hL : L ∈ leviSpaces R V) :
    L ≤ V := by
  obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hL
  exact inf_le_left

/-- Pushing parameters forward, as a continuous linear map. -/
def pushParamL (V : Submodule ℝ E) :
    StrongDual ℝ V →L[ℝ] StrongDual ℝ (mapSub (φ := φ) V) :=
  (ContinuousLinearMap.compL ℝ (mapSub (φ := φ) V) V ℝ).flip
    (LinearMap.toContinuousLinearMap (mapEquiv (φ := φ) V).symm.toLinearMap)

theorem coe_pushParamL (V : Submodule ℝ E) : ⇑(pushParamL (φ := φ) V) = pushParam V := rfl

theorem contDiff_pushParam (V : Submodule ℝ E) : ContDiff ℝ ∞ (pushParam (φ := φ) V) := by
  rw [← coe_pushParamL]
  exact ContinuousLinearMap.contDiff _

section Induced

variable {V b : Submodule ℝ E} (hb : b ≤ V) {c₁ : Finset E → StrongDual ℝ V → ℂ}
  (hext : ∀ S₀ ∈ parabolics R₀ (mapSub (φ := φ) b), ∀ S₁ ∈ parabolics R₀ (mapSub (φ := φ) V),
    S₀ ⊆ S₁ → ∀ Λ₀ : StrongDual ℝ (mapSub (φ := φ) b),
      inducedFamily R₀ (mapSub (φ := φ) b) (mapSub (φ := φ) V) (pushFam φ V c₁) S₀ Λ₀ =
        pushFam φ V c₁ S₁ (extendParam (mapSub (φ := φ) b) (mapSub (φ := φ) V) Λ₀))
include hext

/-- The fine value over a coarse chamber is the induced value of the pushed family. -/
theorem fine_eq_inducedFamily_up {S S₁ : Finset E}
    (hS : S ∈ parabolics (restrictRoots φ R₀) b) (hS₁ : S₁ ∈ parabolics (restrictRoots φ R₀) V)
    (hSS₁ : S ⊆ S₁) (Λ : StrongDual ℝ b) :
    c₁ S₁ (extendParam b V Λ) =
      inducedFamily R₀ (mapSub (φ := φ) b) (mapSub (φ := φ) V) (pushFam φ V c₁) (up φ R₀ S)
        (pushParam b Λ) := by
  rw [hext _ (up_mem_parabolics hS) _ (up_mem_parabolics hS₁) (up_mono hSS₁), pushFam_up hS₁,
    extendParam_pushParam, pullParam_pushParam]

include hb in
theorem inducedFamily_eq_up {S : Finset E} (hS : S ∈ parabolics (restrictRoots φ R₀) b)
    (Λ : StrongDual ℝ b) :
    inducedFamily (restrictRoots φ R₀) b V c₁ S Λ =
      inducedFamily R₀ (mapSub (φ := φ) b) (mapSub (φ := φ) V) (pushFam φ V c₁) (up φ R₀ S)
        (pushParam b Λ) := by
  obtain ⟨S₁, hS₁, hSS₁⟩ := exists_fine_parabolic_extension hb hS
  have h : ∃ S₁ ∈ parabolics (restrictRoots φ R₀) V, S ⊆ S₁ := ⟨S₁, hS₁, hSS₁⟩
  unfold inducedFamily
  rw [dite_eq_left h]
  exact fine_eq_inducedFamily_up hext hS h.choose_spec.1 h.choose_spec.2 Λ

include hb in
theorem pushFam_inducedFamily {S₀ : Finset E₀} (hS₀ : S₀ ∈ parabolics R₀ (mapSub (φ := φ) b)) :
    pushFam φ b (inducedFamily (restrictRoots φ R₀) b V c₁) S₀ =
      inducedFamily R₀ (mapSub (φ := φ) b) (mapSub (φ := φ) V) (pushFam φ V c₁) S₀ := by
  funext Λ₀
  rw [pushFam, inducedFamily_eq_up hb hext (down_mem_parabolics hS₀), up_down hS₀,
    pushParam_pullParam]

end Induced

/-- **Transport of the field-descent formula.** If the field-descent formula holds for a set of
roots `R₀` closed under negation, the image of a fine space `V` and the image of `b ≤ V` under an
isometric embedding, then it holds for the nonzero restrictions of the roots, `V` and `b`. -/
theorem hasFieldDescentFormulaIn_of_mapSub (hR₀ : ∀ γ ∈ R₀, -γ ∈ R₀) {V b : Submodule ℝ E}
    (hb : b ≤ V) (h : HasFieldDescentFormulaIn R₀ (mapSub (φ := φ) V) (mapSub (φ := φ) b)) :
    HasFieldDescentFormulaIn (restrictRoots φ R₀) V b := by
  dsimp only [HasFieldDescentFormulaIn] at h ⊢
  intro c₁ hc₁
  obtain ⟨-, hext, hind, c₀, cQ, ⟨hc₀s, hc₀⟩, hcQ, hid⟩ :=
    h (pushFam φ V c₁) ((isFamily_pushFam_iff V c₁).mpr hc₁)
  have hT := fun S₀ (hS₀ : S₀ ∈ parabolics R₀ (mapSub (φ := φ) b)) =>
    pushFam_inducedFamily hb hext hS₀
  refine ⟨fun S hS => exists_fine_parabolic_extension hb hS, fun S hS S₁ hS₁ hSS₁ Λ => ?_,
    (isFamily_pushFam_iff b _).mp ((isFamily_congr hT).mpr hind),
    fun Λ => c₀ (pushParam b Λ), fun Q Λ => cQ (up φ R₀ Q) (pushParam V Λ), ⟨?_, ?_⟩,
    fun Q hQ => ⟨?_, ?_⟩, ?_⟩
  · rw [inducedFamily_eq_up hb hext hS Λ, ← fine_eq_inducedFamily_up hext hS hS₁ hSS₁ Λ]
  · exact hc₀s.comp (contDiff_pushParam b)
  · intro Λ hΛ
    beta_reduce
    rw [hc₀ _ (fun S₀ hS₀ => ?_), cM_congr (fun S₀ hS₀ => (hT S₀ hS₀).symm), cM_pushFam,
      pullParam_pushParam]
    have hd := down_mem_parabolics hS₀
    rw [← up_down hS₀, theta_up (parabolics_subset_restrictRoots hd), pullParam_pushParam]
    exact hΛ _ hd
  · exact (hcQ _ (up_mem_faces hQ)).1.comp (contDiff_pushParam V)
  · intro Λ hΛ
    beta_reduce
    rw [(hcQ _ (up_mem_faces hQ)).2 _ (fun S₀ hS₀ => ?_), cQM_pushFam hR₀ V c₁ hQ,
      pullParam_pushParam]
    have hl := restrictRoots_leviRoots (φ := φ) hR₀ Q
    have hd := down_mem_parabolics (R₀ := leviRoots R₀ (up φ R₀ Q)) hS₀
    rw [← up_down (R₀ := leviRoots R₀ (up φ R₀ Q)) hS₀,
      theta_up (parabolics_subset_restrictRoots hd), pullParam_pushParam]
    exact hΛ _ (hl ▸ hd)
  · intro ξ hξ hgen Λ
    have hξ₀ : φ ξ ∈ mapSub (φ := φ) V ⊓ (mapSub (φ := φ) b)ᗮ := by
      rw [mapSub_inf_orthogonal]
      exact ⟨ξ, hξ, rfl⟩
    have hgen₀ : ∀ L₀ ∈ leviSpaces R₀ (mapSub (φ := φ) V),
        dDescent (mapSub (φ := φ) b) (coarseCenter R₀ (mapSub (φ := φ) b)) (mapSub (φ := φ) V)
          L₀ ≠ 0 →
        ∀ p₀ : E₀, p₀ ∈ L₀ ⊓ (coarseCenter R₀ (mapSub (φ := φ) b))ᗮ →
          p₀ - φ ξ ∈ mapSub (φ := φ) b ⊓ (coarseCenter R₀ (mapSub (φ := φ) b))ᗮ →
          IsRegular R₀ L₀ p₀ := by
      intro L₀ hL₀ hd p₀ hp₀ hpb₀
      rw [leviSpaces_mapSub hR₀] at hL₀
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hL₀
      rw [← mapSub_coarseCenter, dDescent_mapSub] at hd
      rw [← mapSub_coarseCenter, mapSub_inf_orthogonal] at hp₀ hpb₀
      obtain ⟨p, hp, rfl⟩ := hp₀
      have hpb : p - ξ ∈ b ⊓ (coarseCenter (restrictRoots φ R₀) b)ᗮ := by
        rw [← mem_mapSub_iff (φ := φ), map_sub]
        exact hpb₀
      exact (isRegular_mapSub_iff L p).mpr (hgen L hL hd p hp hpb)
    beta_reduce
    rw [hid (φ ξ) hξ₀ hgen₀ (pushParam b Λ), sum_leviSpaces_mapSub hR₀]
    apply Finset.sum_congr rfl
    intro L hL
    rw [← mapSub_coarseCenter, dDescent_mapSub]
    by_cases hd : dDescent b (coarseCenter (restrictRoots φ R₀) b) V L = 0
    · simp [hd]
    · rw [descentSection_mapSub (z := coarseCenter (restrictRoots φ R₀) b) inf_le_left hb (coarseCenter_le_of_mem_leviSpaces hb hL)
        (le_of_mem_leviSpaces' hL) hd hξ, extendParam_pushParam]

/-! ### Central and special subspaces -/

omit [FiniteDimensional ℝ E₀] in
theorem starProjection_mapSub (W : Submodule ℝ E) (x : E) :
    (mapSub (φ := φ) W).starProjection (φ x) = φ (W.starProjection x) := by
  apply eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨_, W.starProjection_apply_mem x, rfl⟩
  rintro _ ⟨w, hw, rfl⟩
  change ⟪φ x - φ (W.starProjection x), φ w⟫ = 0
  rw [← map_sub, LinearIsometry.inner_map_map]
  exact W.starProjection_inner_eq_zero x w hw

/-- When the central space of `R₀` lies in the image, it is the image of the central space of
the restricted roots. -/
theorem centralSpace_eq_mapSub (hZ₀ : centralSpace R₀ ≤ mapSub (φ := φ) ⊤) :
    centralSpace R₀ = mapSub (φ := φ) (centralSpace (restrictRoots φ R₀)) := by
  have h := mapSub_inf_iInf (φ := φ) ⊤ R₀
  rw [top_inf_eq] at h
  exact (inf_eq_right.mpr hZ₀).symm.trans h

theorem isCentreSplit_mapSub (hZ₀ : centralSpace R₀ ≤ mapSub (φ := φ) ⊤) {b : Submodule ℝ E}
    (hZ : ∀ x ∈ b, (centralSpace (restrictRoots φ R₀)).starProjection x ∈ b) :
    CentreReduction.IsCentreSplit R₀ (mapSub (φ := φ) b) := by
  rintro _ ⟨x, hx, rfl⟩
  change (centralSpace R₀).starProjection (φ x) ∈ mapSub (φ := φ) b
  rw [centralSpace_eq_mapSub hZ₀, starProjection_mapSub]
  exact ⟨_, hZ x hx, rfl⟩

theorem coe_restrictedRoot_top (y : E) : (restrictedRoot (⊤ : Submodule ℝ E) y : E) = y := by
  change (⊤ : Submodule ℝ E).starProjection y = y
  exact starProjection_eq_self_iff.mpr Submodule.mem_top

/-- **Special subspaces under restriction.** If the weighted sums of the restricted roots over
each nonzero restriction to `b` lie in `b`, where a restricted root is weighted by the total weight
of the roots restricting to it, then the image of `b` is special for the image of the whole
space. -/
theorem isSpecialSubspace_mapSub {b : Submodule ℝ E} {m₀ : E₀ → ℝ} (hm₀ : ∀ γ ∈ R₀, 0 < m₀ γ)
    (hs : ∀ β : b, β ≠ 0 →
      (∑ α ∈ (restrictRoots φ R₀).filter (fun α => restrictedRoot b α = β),
        (∑ γ ∈ R₀.filter (fun γ => res φ γ = α), m₀ γ) • α) ∈ b) :
    IsSpecialSubspace R₀ (mapSub (φ := φ) b) (mapSub (φ := φ) ⊤) m₀ := by
  refine ⟨hm₀, fun β₀ hβ₀ => ?_⟩
  let β : b := (mapEquiv (φ := φ) b).symm β₀
  have hββ : mapEquiv (φ := φ) b β = β₀ := LinearEquiv.apply_symm_apply _ _
  have hβ : β ≠ 0 := fun h => hβ₀ (by rw [← hββ, h, map_zero])
  let s := R₀.filter (fun γ => restrictedRoot b (res φ γ) = β)
  let t := (restrictRoots φ R₀).filter (fun α => restrictedRoot b α = β)
  have hfilter : R₀.filter (fun γ => restrictedRoot (mapSub (φ := φ) b) γ = β₀) = s := by
    apply Finset.filter_congr
    intro γ _
    rw [restrictedRoot_mapSub, ← hββ]
    exact (mapEquiv (φ := φ) b).injective.eq_iff
  have hmaps : ∀ γ ∈ s, res φ γ ∈ t := by
    intro γ hγ
    obtain ⟨hγR, hγβ⟩ := Finset.mem_filter.mp hγ
    refine Finset.mem_filter.mpr ⟨mem_restrictRoots.mpr ⟨fun h0 => hβ ?_, γ, hγR, rfl⟩, hγβ⟩
    rw [← hγβ, h0]
    exact Subtype.ext (by simp [restrictedRoot])
  have hsum : ∑ γ ∈ s, m₀ γ • res φ γ =
      ∑ α ∈ t, (∑ γ ∈ R₀.filter (fun γ => res φ γ = α), m₀ γ) • α := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro α hα
    rw [Finset.sum_smul]
    have hst : s.filter (fun γ => res φ γ = α) = R₀.filter (fun γ => res φ γ = α) := by
      ext γ
      simp only [Finset.mem_filter, s]
      constructor
      · rintro ⟨⟨hγ, -⟩, he⟩
        exact ⟨hγ, he⟩
      · rintro ⟨hγ, he⟩
        exact ⟨⟨hγ, he ▸ (Finset.mem_filter.mp hα).2⟩, he⟩
    rw [hst]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [(Finset.mem_filter.mp hγ).2]
  rw [hfilter]
  have he : ∑ γ ∈ s, m₀ γ • (mapSub (φ := φ) ⊤).starProjection γ =
      φ (∑ γ ∈ s, m₀ γ • res φ γ) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro γ _
    rw [map_smul]
    congr 1
    change (restrictedRoot (mapSub (φ := φ) ⊤) γ : E₀) = _
    rw [coe_restrictedRoot_mapSub, coe_restrictedRoot_top]
  rw [he, hsum]
  exact ⟨_, hs β hβ, rfl⟩

/-- **The field-descent formula from a root set.** Let `R₀` be a root set in `E₀` and `φ` an
isometric embedding of `E` onto a Levi flat of `R₀`. If `b ⊆ E` is preserved by the orthogonal
projection to the central space of the restricted roots and the weighted sums of the restricted
roots over each nonzero restriction to `b`, with weights the total positive weights `m₀` of the
roots restricting to them, lie in `b`, then the field-descent formula holds for the restricted
roots and `b`. -/
theorem hasFieldDescentFormula_of_restrictRoots (hR₀ : IsRootSet R₀)
    (ha₁ : IsLeviSpace R₀ (mapSub (φ := φ) ⊤)) {b : Submodule ℝ E}
    (hZ : ∀ x ∈ b, (centralSpace (restrictRoots φ R₀)).starProjection x ∈ b)
    {m₀ : E₀ → ℝ} (hm₀ : ∀ γ ∈ R₀, 0 < m₀ γ)
    (hs : ∀ β : b, β ≠ 0 →
      (∑ α ∈ (restrictRoots φ R₀).filter (fun α => restrictedRoot b α = β),
        (∑ γ ∈ R₀.filter (fun γ => res φ γ = α), m₀ γ) • α) ∈ b) :
    HasFieldDescentFormula (restrictRoots φ R₀) b :=
  hasFieldDescentFormula_iff_top.mpr <|
    hasFieldDescentFormulaIn_of_mapSub (fun _ hγ => hR₀.neg_mem hγ) le_top <|
      hasFieldDescentFormulaIn hR₀ ha₁ (Submodule.map_mono le_top)
        (isCentreSplit_mapSub (centralSpace_le_of_levi ha₁) hZ) (isSpecialSubspace_mapSub hm₀ hs)

end RootRestriction

end Langlands.GMFamily
