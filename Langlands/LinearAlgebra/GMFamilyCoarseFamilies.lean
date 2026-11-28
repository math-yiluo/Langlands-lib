import Langlands.LinearAlgebra.GMFamilyInducedValues
import Langlands.LinearAlgebra.GMFamiliesFaces
import Langlands.LinearAlgebra.GMFamilyLeviRootBasis
import Langlands.LinearAlgebra.GMFamilySmoothExtension

/-! # Induced families on arbitrary subspaces and families of Levi components -/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open Classical Submodule

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a b a₁ : Submodule ℝ E}

/-- Extension of parameters through the orthogonal projection, as a continuous linear map. -/
def extendParamL (b a₁ : Submodule ℝ E) : StrongDual ℝ b →L[ℝ] StrongDual ℝ a₁ :=
  (ContinuousLinearMap.compL ℝ a₁ b ℝ).flip (b.orthogonalProjectionOnto.comp a₁.subtypeL)

theorem coe_extendParamL (b a₁ : Submodule ℝ E) : ⇑(extendParamL b a₁) = extendParam b a₁ := rfl

theorem contDiff_extendParam (b a₁ : Submodule ℝ E) : ContDiff ℝ ∞ (extendParam b a₁) := by
  rw [← coe_extendParamL]
  exact ContinuousLinearMap.contDiff _

omit [FiniteDimensional ℝ E] in
private theorem neg_mem_posSet_iff (hR : IsRootSet R) {x p : E} :
    -x ∈ posSet R p ↔ x ∈ R ∧ ⟪x, p⟫ < 0 := by
  rw [mem_posSet_iff, neg_mem_rootSet_iff hR, inner_neg_left, neg_pos]

/-- **Induced families are families.** For a root set, a subspace `b ≤ a₁` and a family on
`a₁`, the induced family on `b` is a family; `b` need not be a Levi flat. Two fine chambers over
adjacent coarse chambers are joined by a gallery whose walls are roots with restriction to `b`
proportional to the common wall. -/
theorem isFamily_inducedFamily (hR : IsRootSet R) (hb : b ≤ a₁)
    {c₁ : Finset E → StrongDual ℝ a₁ → ℂ} (hc₁ : IsFamily R a₁ c₁) :
    IsFamily R b (inducedFamily R b a₁ c₁) := by
  refine ⟨fun S hS => ?_, fun S hS S' hS' v hadj Λ hΛ => ?_⟩
  · obtain ⟨P₁, hP₁, hSP⟩ := exists_fine_parabolic_extension hb hS
    have he : inducedFamily R b a₁ c₁ S = c₁ P₁ ∘ extendParam b a₁ := by
      funext Λ
      exact inducedFamily_eq_of_extension hR hb hc₁ hS hP₁ hSP Λ
    rw [he]
    exact (hc₁.1 P₁ hP₁).comp (contDiff_extendParam b a₁)
  obtain ⟨P₁, hP₁, h₁⟩ := exists_fine_parabolic_extension hb hS
  obtain ⟨P₂, hP₂, h₂⟩ := exists_fine_parabolic_extension hb hS'
  rw [inducedFamily_eq_of_extension hR hb hc₁ hS hP₁ h₁,
    inducedFamily_eq_of_extension hR hb hc₁ hS' hP₂ h₂]
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hS
  obtain ⟨q₁, hq₁, rfl⟩ := mem_parabolics_iff.mp hP₁
  obtain ⟨q₂, hq₂, rfl⟩ := mem_parabolics_iff.mp hP₂
  have hsame := hadj.2.2
  apply family_eq_of_protected_signs hR hc₁ (fun r => ∀ t : ℝ, restrictedRoot b r ≠ t • v)
    hq₁ hq₂
  · intro r hr _ hkeep
    have hr0 : restrictedRoot b r ≠ 0 := fun h => hkeep 0 (by rw [h, zero_smul])
    rcases lt_or_gt_of_ne (hp.2 r hr hr0) with hn | hpos
    · have hkeep' : ∀ t : ℝ, restrictedRoot b (-r) ≠ t • v := by
        intro t ht
        apply hkeep (-t)
        have h := congrArg Neg.neg ht
        simp only [restrictedRoot, map_neg, neg_neg] at h
        rw [neg_smul]
        exact h
      have hneg : -r ∈ posSet R p := (neg_mem_posSet_iff hR).mpr ⟨hr, hn⟩
      have hneg' := (hsame (-r) (hR.neg_mem hr) hkeep').mp hneg
      exact mul_pos_of_neg_of_neg ((neg_mem_posSet_iff hR).mp (h₁ hneg)).2
        ((neg_mem_posSet_iff hR).mp (h₂ hneg')).2
    · have hpp : r ∈ posSet R p := mem_posSet_iff.mpr ⟨hr, hpos⟩
      have hpp' := (hsame r hr hkeep).mp hpp
      exact mul_pos (mem_posSet_iff.mp (h₁ hpp)).2 (mem_posSet_iff.mp (h₂ hpp')).2
  · intro r _ _ hkeep
    simp only [not_forall, not_not] at hkeep
    obtain ⟨t, ht⟩ := hkeep
    change Λ (restrictedRoot b (restrictedRoot a₁ r : E)) = 0
    rw [restrictedRoot_nested hb, ht, map_smul, hΛ, smul_zero]

omit [FiniteDimensional ℝ E] in
/-- The roots of a Levi component cut out the same flat at a point as all roots, when the
point is a defining point of a Levi flat containing the face. -/
theorem isLeviSpace_leviRoots_of_mem_faces (hR : IsRootSet R) (ha : IsLeviSpace R a) {Q : Finset E}
    (hQ : Q ∈ faces R a) : IsLeviSpace (leviRoots R Q) a := by
  obtain ⟨h₀, rfl⟩ := ha
  obtain ⟨q, hq, rfl⟩ := mem_faces_iff.mp hQ
  refine ⟨h₀, ?_⟩
  have hfilter : (leviRoots R (posSet R q)).filter (fun α => ⟪α, h₀⟫ = 0) =
      R.filter (fun α => ⟪α, h₀⟫ = 0) := by
    ext α
    simp only [Finset.mem_filter, mem_leviRoots_posSet hR]
    constructor
    · rintro ⟨⟨hα, _⟩, h0⟩
      exact ⟨hα, h0⟩
    · rintro ⟨hα, h0⟩
      exact ⟨⟨hα, (mem_leviSpaceOf_iff.mp hq) α hα h0⟩, h0⟩
  unfold leviSpaceOf
  rw [hfilter]

omit [FiniteDimensional ℝ E] in
theorem isRootSet_leviRoots (hR : IsRootSet R) {Q : Finset E} (hQ : Q ∈ faces R a) :
    IsRootSet (leviRoots R Q) := by
  obtain ⟨q, _, rfl⟩ := mem_faces_iff.mp hQ
  exact isRootSet_leviRoots_posSet hR q

/-- Simple roots of a chamber of the Levi component of a face remain simple for the chamber
above the face. -/
private theorem mem_simpleRoots_union (hR : IsRootSet R) {Q S : Finset E}
    (hQ : Q ∈ faces R a) (hS : S ∈ parabolics (leviRoots R Q) a) {v : a}
    (hv : v ∈ simpleRoots a S) : v ∈ simpleRoots a (Q ∪ S) := by
  obtain ⟨q, hq, rfl⟩ := mem_faces_iff.mp hQ
  have hSl : S ⊆ leviRoots R (posSet R q) := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  obtain ⟨hvr, hvs⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hvr
    exact Finset.mem_image.mpr ⟨r, Finset.mem_union_right _ hr, rfl⟩
  · rintro ⟨u, hu, w, hw, he⟩
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hvr
    obtain ⟨ru, hru, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨rw, hrw, rfl⟩ := Finset.mem_image.mp hw
    have hpair (x : E) : ⟪(restrictedRoot a x : E), q⟫ = ⟪x, q⟫ := inner_restrictedRoot hq
    have hr0 : ⟪r, q⟫ = 0 := ((mem_leviRoots_posSet hR).mp (hSl hr)).2
    have hnn (x : E) (hx : x ∈ posSet R q ∪ S) : 0 ≤ ⟪x, q⟫ := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (mem_posSet_iff.mp hx).2.le
      · exact ((mem_leviRoots_posSet hR).mp (hSl hx)).2.ge
    have hsum : ⟪r, q⟫ = ⟪ru, q⟫ + ⟪rw, q⟫ := by
      rw [← hpair r, he, Submodule.coe_add, inner_add_left, hpair, hpair]
    have hu0 : ⟪ru, q⟫ = 0 := by linarith [hnn ru hru, hnn rw hrw]
    have hw0 : ⟪rw, q⟫ = 0 := by linarith [hnn ru hru, hnn rw hrw]
    have hinS (x : E) (hx : x ∈ posSet R q ∪ S) (h0 : ⟪x, q⟫ = 0) : x ∈ S := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ((mem_posSet_iff.mp hx).2.ne' h0).elim
      · exact hx
    exact hvs ⟨_, Finset.mem_image.mpr ⟨ru, hinS ru hru hu0, rfl⟩,
      _, Finset.mem_image.mpr ⟨rw, hinS rw hrw hw0, rfl⟩, he⟩

/-- **Families of a Levi component.** For a face `Q`, the chambers of the Levi component of `Q`
together with `Q` give a family for the roots of that Levi component. -/
theorem isFamily_union (hR : IsRootSet R) {Q : Finset E} (hQ : Q ∈ faces R a)
    {c : Finset E → StrongDual ℝ a → ℂ} (hc : IsFamily R a c) :
    IsFamily (leviRoots R Q) a (fun S => c (Q ∪ S)) := by
  refine ⟨fun S hS => hc.1 _ (union_mem_parabolics hR hQ hS),
    fun S hS S' hS' v hadj Λ hΛ => ?_⟩
  apply hc.2 _ (union_mem_parabolics hR hQ hS) _ (union_mem_parabolics hR hQ hS') v _ Λ hΛ
  obtain ⟨hv, hnv, hsame⟩ := hadj
  refine ⟨mem_simpleRoots_union hR hQ hS hv, mem_simpleRoots_union hR hQ hS' hnv, ?_⟩
  intro α hα hne
  have hSl : S ⊆ leviRoots R Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hSl' : S' ⊆ leviRoots R Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hS').1
  simp only [Finset.mem_union]
  by_cases hαQ : α ∈ Q
  · exact iff_of_true (Or.inl hαQ) (Or.inl hαQ)
  by_cases hl : α ∈ leviRoots R Q
  · have := hsame α hl hne
    simp only [hαQ, false_or]
    exact this
  · have hS0 : α ∉ S := fun h => hl (hSl h)
    have hS0' : α ∉ S' := fun h => hl (hSl' h)
    simp only [hαQ, hS0, hS0', or_self]

/-- **Smooth relative supplementary functions.** For a root set and a Levi flat `a`, the relative
supplementary functions of a family at the faces have smooth representatives agreeing with them
wherever the denominators of the Levi component do not vanish. Off the faces the representative
is zero. -/
theorem exists_smooth_cQM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {R : Finset E} {a : Submodule ℝ E}
    (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {c : Finset E → StrongDual ℝ a → ℂ} (hc : IsFamily R a c) :
    ∃ cQ : Finset E → StrongDual ℝ a → ℂ, (∀ Q, ContDiff ℝ ∞ (cQ Q)) ∧ ∀ Q ∈ faces R a,
      ∀ Λ : StrongDual ℝ a, (∀ S ∈ parabolics (leviRoots R Q) a, theta a S Λ ≠ 0) →
        cQ Q Λ = cQM R a c Q Λ := by
  have hex (Q : Finset E) (hQ : Q ∈ faces R a) := smoothExtension (leviRoots R Q) a
    (isRootSet_leviRoots hR hQ) (isLeviSpace_leviRoots_of_mem_faces hR ha hQ) _ (isFamily_union hR hQ hc)
  refine ⟨fun Q => if hQ : Q ∈ faces R a then (hex Q hQ).choose else 0, fun Q => ?_,
    fun Q hQ Λ hΛ => ?_⟩
  · by_cases hQ : Q ∈ faces R a
    · simp only [hQ, ↓reduceDIte]
      exact (hex Q hQ).choose_spec.1
    · simp only [hQ, ↓reduceDIte]
      exact contDiff_const
  · simp only [hQ, ↓reduceDIte]
    exact (hex Q hQ).choose_spec.2 Λ hΛ

end Langlands.GMFamily
