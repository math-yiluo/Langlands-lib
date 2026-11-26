import Langlands.LinearAlgebra.GMFamiliesStatement
import Langlands.LinearAlgebra.GMFamilySplittingVertices

/-! # Alternate splitting for `(G, M)`-families -/

noncomputable section

open Classical Finset
open scoped RealInnerProductSpace

universe u

namespace Langlands.GMFamily

open AffineBases

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

private def faceWeight (R : Finset E) (a : Submodule ℝ E) (Λ : StrongDual ℝ a) (Q P : Finset E) : ℂ :=
  if Q ⊆ P then (theta a (P ∩ leviRoots R Q) Λ)⁻¹ else 0

private theorem cQM_eq_sum (hR : IsRootSet R) (x : a) (c : Finset E → StrongDual ℝ a → ℂ)
    (Λ : StrongDual ℝ a) : cQM R a c (posSet R (x : E)) Λ =
      ∑ P ∈ parabolics R a, c P Λ * faceWeight R a Λ (posSet R (x : E)) P := by
  let Q := posSet R (x : E)
  let T := (parabolics R a).filter (Q ⊆ ·)
  have he : ∑ P ∈ parabolics R a, c P Λ * faceWeight R a Λ Q P =
      ∑ P ∈ T, c P Λ * (theta a (P ∩ leviRoots R Q) Λ)⁻¹ := by
    rw [sum_filter]
    apply sum_congr rfl
    intro P _
    by_cases h : Q ⊆ P <;> simp [faceWeight, h]
  rw [he]
  unfold cQM
  apply sum_nbij (fun S => Q ∪ S)
  · intro S hS
    exact mem_filter.mpr ⟨(union_parabolic_of_local hR x hS).1, subset_union_left⟩
  · intro S hS S' hS' h
    have h₁ := (union_parabolic_of_local hR x hS).2
    have h₂ := (union_parabolic_of_local hR x hS').2
    change posSet R (x : E) ∪ S = posSet R (x : E) ∪ S' at h
    exact h₁.symm.trans ((congrArg (fun T => T ∩ leviRoots R (posSet R (x : E))) h).trans h₂)
  · intro P hP
    obtain ⟨hp, hqp⟩ := mem_filter.mp hP
    obtain ⟨hS, heq⟩ := inter_leviRoots_parabolic hR hp x hqp
    exact ⟨_, hS, heq⟩
  · intro S hS
    rw [(union_parabolic_of_local hR x hS).2]

private theorem theta_inv_eq {P : Finset E} (Λ : StrongDual ℝ a) :
    (theta a P Λ)⁻¹ = (gramVolume (fun i : simpleRoots a P => (i : E)) : ℂ) /
      ∏ i : simpleRoots a P, Complex.I * (Λ (i : a) : ℂ) := by
  simp only [theta, thetaOf, mul_inv, inv_inv, div_eq_mul_inv]

private theorem faceWeight_eq_rootWeight (hR : IsRootSet R) {P : Finset E} (hP : P ∈ parabolics R a)
    (x : a) (hx : posSet R (x : E) ⊆ P) (Λ : StrongDual ℝ a) :
    faceWeight R a Λ (posSet R (x : E)) P =
      rootWeight (univ.filter fun i : simpleRoots a P => ⟪(i : a), x⟫ = 0) Λ := by
  rw [faceWeight, ite_eq_left hx, theta_inv_eq, simpleRoots_inter_leviRoots hR hP x hx, rootWeight]
  let I := (univ : Finset (simpleRoots a P)).filter fun (i : simpleRoots a P) => ⟪i.val, x⟫ = 0
  let J := (simpleRoots a P).filter fun i => ⟪i, x⟫ = 0
  let e : (I : Type _) ≃ (J : Type _) := Equiv.ofBijective
    (fun (i : I) => ⟨i.val.val, mem_filter.mpr ⟨i.val.property, (mem_filter.mp i.property).2⟩⟩)
    ⟨fun i j h => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : J => z.val) h,
      fun j => by
        obtain ⟨hj, hjx⟩ := mem_filter.mp j.property
        exact ⟨⟨⟨j.val, hj⟩, mem_filter.mpr ⟨mem_univ _, hjx⟩⟩, Subtype.ext rfl⟩⟩
  have hgram : gramVolume (fun i : J => ((i : a) : E)) =
      gramVolume (fun i : I => (i.val.val : E)) :=
    (gramVolume_reindex e (fun i : J => ((i : a) : E))).symm
  have hprod : (∏ i : J, Complex.I * (Λ (i : a) : ℂ)) =
      ∏ i : I, Complex.I * (Λ i.val.val : ℂ) :=
    (e.prod_comp _).symm
  change ((gramVolume (fun i : J => ((i : a) : E)) : ℝ) : ℂ) /
      (∏ i : J, Complex.I * (Λ (i : a) : ℂ)) = _
  rw [hgram, hprod]

private theorem weight_left_eq_theta_inv (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) (Λ : StrongDual ℝ a) :
    normalizedWeight (pairedNormals hR ha hP hP) (effectiveParam R a Λ) (leftBasisIndex hR ha hP) =
      (theta a P Λ)⁻¹ := by
  let B := leftBasisIndex hR ha hP
  let e : simpleRoots a P ≃ B.val := Equiv.ofBijective
    (fun i => ⟨.inl i, mem_map.mpr ⟨i, mem_univ _, rfl⟩⟩)
    ⟨fun i j h => Sum.inl.inj (congrArg Subtype.val h),
      fun j => by obtain ⟨i, -, hi⟩ := mem_map.mp j.property; exact ⟨i, Subtype.ext hi⟩⟩
  rw [normalizedWeight, theta_inv_eq, ← gramVolume_reindex e _, ← e.prod_comp]
  rfl

private def pairSectionWeight (R : Finset E) (a : Submodule ℝ E) (ξ : E) (Λ : StrongDual ℝ a)
    (L : Submodule ℝ E × Submodule ℝ E) (P : Finset E × Finset E) : ℂ :=
  (dCoeff R a L.1 L.2 : ℂ) * faceWeight R a Λ (splittingSection R ξ L.1 L.2).1 P.1 *
    faceWeight R a Λ (splittingSection R ξ L.1 L.2).2 P.2

private theorem sectionWeight_eq_normalizedWeight (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P₁ P₂ : Finset E} (h₁ : P₁ ∈ parabolics R a) (h₂ : P₂ ∈ parabolics R a)
    (ξ : effectiveSpace R a) (hξ : RegularDisplacement R a (ξ : E)) (Λ : StrongDual ℝ a)
    (B : BasisIndex (pairedNormals hR ha h₁ h₂))
    (hB : Feasible (pairedNormals hR ha h₁ h₂) B (splittingIntercepts hR ha h₁ h₂ ξ)) :
    pairSectionWeight R a ξ Λ (vertexFlats hR ha h₁ h₂ B) (P₁, P₂) =
      normalizedWeight (pairedNormals hR ha h₁ h₂) (effectiveParam R a Λ) B := by
  let v := pairedNormals hR ha h₁ h₂
  let b := splittingIntercepts hR ha h₁ h₂ ξ
  let x := splittingVertex hR ha h₁ h₂ ξ B
  let y₁ : a := ⟨(x + ξ : effectiveSpace R a), (x + ξ).property.1⟩
  let y₂ : a := ⟨(x - ξ : effectiveSpace R a), (x - ξ).property.1⟩
  have hreg := regular_splittingIntercepts hR ha h₁ h₂ ξ hξ
  have hsub := (feasible_iff_section_subset hR ha h₁ h₂ ξ hξ B).mp hB
  rw [vertex_section_eq hR ha h₁ h₂ ξ B] at hsub
  have hzero (i : NormalIndices a P₁ P₂) : slack v B i b = 0 ↔ i ∈ B.val :=
    ⟨fun e => Classical.byContradiction (fun hi => hreg B i hi e),
      fun hi => by rw [slack_eq_zero_of_mem v B hi, LinearMap.zero_apply]⟩
  have hleft : univ.filter (fun i : simpleRoots a P₁ => ⟪(i : a), y₁⟫ = 0) = B.val.toLeft := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_toLeft]
    have he : slack v B (.inl i) b = ⟪(i : a), y₁⟫ := slack_inl_eq hR ha h₁ h₂ ξ B i
    rw [← he]
    exact hzero (.inl i)
  have hright : univ.filter (fun i : simpleRoots a P₂ => ⟪(i : a), y₂⟫ = 0) = B.val.toRight := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_toRight]
    have he : slack v B (.inr i) b = ⟪(i : a), y₂⟫ := slack_inr_eq hR ha h₁ h₂ ξ B i
    rw [← he]
    exact hzero (.inr i)
  unfold pairSectionWeight
  rw [vertex_section_eq hR ha h₁ h₂ ξ B]
  change (dCoeff R a (normalFlat P₁ B.val.toLeft) (normalFlat P₂ B.val.toRight) : ℂ) *
    faceWeight R a Λ (posSet R (y₁ : E)) P₁ * faceWeight R a Λ (posSet R (y₂ : E)) P₂ = _
  rw [faceWeight_eq_rootWeight hR h₁ y₁ hsub.1, faceWeight_eq_rootWeight hR h₂ y₂ hsub.2, hleft, hright]
  exact (normalizedWeight_disjSum hR ha h₁ h₂ _ _ Λ B toLeft_disjSum_toRight.symm).symm

private theorem sum_pairSectionWeight_eq (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P₁ P₂ : Finset E} (h₁ : P₁ ∈ parabolics R a) (h₂ : P₂ ∈ parabolics R a)
    (ξ : effectiveSpace R a) (hξ : RegularDisplacement R a (ξ : E)) (Λ : StrongDual ℝ a)
    (hΛ : ∀ α ∈ R, restrictedRoot a α ≠ 0 → Λ (restrictedRoot a α) ≠ 0) :
    (∑ L ∈ (leviSpaces R a).product (leviSpaces R a), pairSectionWeight R a ξ Λ L (P₁, P₂)) =
      if P₁ = P₂ then (theta a P₁ Λ)⁻¹ else 0 := by
  let v := pairedNormals hR ha h₁ h₂
  let b := splittingIntercepts hR ha h₁ h₂ ξ
  let ℓ := effectiveParam R a Λ
  let T := (leviSpaces R a).product (leviSpaces R a)
  let f (L : Submodule ℝ E × Submodule ℝ E) : Prop := dCoeff R a L.1 L.2 ≠ 0 ∧
    (splittingSection R ξ L.1 L.2).1 ⊆ P₁ ∧ (splittingSection R ξ L.1 L.2).2 ⊆ P₂
  have hred : (∑ L ∈ T, pairSectionWeight R a ξ Λ L (P₁, P₂)) =
      ∑ L ∈ T.filter f, pairSectionWeight R a ξ Λ L (P₁, P₂) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro L _
    by_cases hf : f L
    · rw [ite_eq_left hf]
    · rw [ite_eq_right hf]
      by_cases hd : dCoeff R a L.1 L.2 = 0
      · simp [pairSectionWeight, hd]
      · have h : ¬ ((splittingSection R ξ L.1 L.2).1 ⊆ P₁ ∧ (splittingSection R ξ L.1 L.2).2 ⊆ P₂) :=
          fun hp => hf ⟨hd, hp⟩
        by_cases hp : (splittingSection R ξ L.1 L.2).1 ⊆ P₁
        · have hq : ¬ ((splittingSection R ξ L.1 L.2).2 ⊆ P₂) := fun hq => h ⟨hp, hq⟩
          rw [pairSectionWeight, faceWeight, faceWeight, ite_eq_left hp, ite_eq_right hq, mul_zero]
        · simp [pairSectionWeight, faceWeight, hp]
  have hbij : (∑ B ∈ (univ : Finset (BasisIndex v)).filter (fun B => Feasible v B b), normalizedWeight v ℓ B) =
      ∑ L ∈ T.filter f, pairSectionWeight R a ξ Λ L (P₁, P₂) := by
    apply sum_nbij (vertexFlats hR ha h₁ h₂)
    · intro B hb
      have hB := (mem_filter.mp hb).2
      obtain ⟨hL₁, hL₂, hd⟩ := vertexFlats_mem_and_dCoeff hR ha h₁ h₂ B
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hL₁, hL₂⟩, hd,
        (feasible_iff_section_subset hR ha h₁ h₂ ξ hξ B).mp hB⟩
    · intro B _ C _ hBC
      exact vertexFlats_injective hR ha h₁ h₂ ξ hξ hBC
    · intro L hL
      obtain ⟨hLT, hd, hp, hq⟩ := mem_filter.mp hL
      obtain ⟨hL₁, hL₂⟩ := mem_product.mp hLT
      obtain ⟨B, hb, he⟩ := exists_feasible_vertex_of_sections hR ha h₁ h₂ ξ hξ hL₁ hL₂ hd hp hq
      exact ⟨B, mem_filter.mpr ⟨mem_univ _, hb⟩, he⟩
    · intro B hb
      exact (sectionWeight_eq_normalizedWeight hR ha h₁ h₂ ξ hξ Λ B (mem_filter.mp hb).2).symm
  rw [hred, ← hbij, sum_filter]
  have hℓ (i : NormalIndices a P₁ P₂) : ℓ (v i) ≠ 0 := by
    have hsimple {P : Finset E} (hP : P ∈ parabolics R a) (i : simpleRoots a P) :
        ℓ (simpleNormal hR ha hP i) ≠ 0 := by
      obtain ⟨α, hα, hi⟩ := mem_image.mp (mem_filter.mp i.property).1
      have hαR := mem_powerset.mp (mem_filter.mp hP).1 hα
      have hi₀ : restrictedRoot a α ≠ 0 := by
        obtain ⟨x, hx, hPx⟩ := (mem_filter.mp hP).2
        rw [hPx] at hα
        exact fun h => (mem_filter.mp hα).2.ne' ((restrictedRoot_eq_zero_iff_forall_inner a α).mp h x hx.1)
      rw [effectiveParam_simpleNormal, ← hi]
      exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hΛ α hαR hi₀))
    cases i with
    | inl i => exact hsimple h₁ i
    | inr i => exact hsimple h₂ i
  have hb := regular_splittingIntercepts hR ha h₁ h₂ ξ hξ
  dsimp only [v, b, ℓ] at *
  by_cases he : P₁ = P₂
  · subst P₂
    rw [ite_eq_left rfl, sum_normalizedWeight_eq_left hR ha h₁ _ hℓ _ hb, weight_left_eq_theta_inv]
  · rw [ite_eq_right he]
    exact sum_normalizedWeight_eq_zero_of_ne hR ha h₁ h₂ he _ hℓ _ hb

private theorem weighted_pair_eq_sum (hR : IsRootSet R) (ha : IsLeviSpace R a)
    (c d : Finset E → StrongDual ℝ a → ℂ) (ξ : effectiveSpace R a) (Λ : StrongDual ℝ a)
    (L : Submodule ℝ E × Submodule ℝ E) (hL : L ∈ (leviSpaces R a).product (leviSpaces R a)) :
    (dCoeff R a L.1 L.2 : ℂ) * cQM R a c (splittingSection R ξ L.1 L.2).1 Λ *
      cQM R a d (splittingSection R ξ L.1 L.2).2 Λ =
    ∑ P ∈ (parabolics R a).product (parabolics R a),
      c P.1 Λ * d P.2 Λ * pairSectionWeight R a ξ Λ L P := by
  by_cases hd : dCoeff R a L.1 L.2 = 0
  · simp [pairSectionWeight, hd]
  obtain ⟨hL₁, hL₂⟩ := mem_product.mp hL
  obtain ⟨x₁, x₂, hx₁, hx₂, he, hu⟩ := exists_unique_splitting_points hR ha hL₁ hL₂ hd ξ
  let y₁ : a := ⟨x₁, (mem_leviSpaces_iff hR ha L.1).mp hL₁ |>.1 hx₁.1⟩
  let y₂ : a := ⟨x₂, (mem_leviSpaces_iff hR ha L.2).mp hL₂ |>.1 hx₂.1⟩
  unfold pairSectionWeight
  rw [splittingSection_eq_of_unique hx₁ hx₂ he hu, cQM_eq_sum hR y₁, cQM_eq_sum hR y₂, product_eq_sprod, sum_product]
  rw [mul_assoc, sum_mul, mul_sum]
  apply sum_congr rfl
  intro P₁ _
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro P₂ _
  ring

/-- Arthur's alternate splitting formula at all parameters avoiding the finite set of
nonzero restricted-root hyperplanes. -/
theorem alternateSplittingFormula : AlternateSplittingFormulaStatement.{u} := by
  intro E _ _ _ R a hR ha c d _ _ ξ hξ hreg
  let y : effectiveSpace R a := ⟨ξ, hξ⟩
  let E₀ := ((R.image (restrictedRoot a)).erase 0)
  refine ⟨E₀, notMem_erase _ _, fun Λ hΛ => ?_⟩
  have hnon (α : E) (hα : α ∈ R) (hα₀ : restrictedRoot a α ≠ 0) : Λ (restrictedRoot a α) ≠ 0 :=
    hΛ _ (mem_erase.mpr ⟨hα₀, mem_image_of_mem _ hα⟩)
  let T := (leviSpaces R a).product (leviSpaces R a)
  let S := (parabolics R a).product (parabolics R a)
  let f (L : Submodule ℝ E × Submodule ℝ E) : ℂ :=
    (dCoeff R a L.1 L.2 : ℂ) * cQM R a c (splittingSection R ξ L.1 L.2).1 Λ *
      cQM R a d (splittingSection R ξ L.1 L.2).2 Λ
  symm
  change (∑ L₁ ∈ leviSpaces R a, ∑ L₂ ∈ leviSpaces R a, f (L₁, L₂)) = _
  calc
    _ = ∑ L ∈ T, f L := (sum_product (leviSpaces R a) (leviSpaces R a) f).symm
    _ = ∑ L ∈ T, ∑ P ∈ S, c P.1 Λ * d P.2 Λ * pairSectionWeight R a y Λ L P := by
      exact sum_congr rfl (fun L hL => weighted_pair_eq_sum hR ha c d y Λ L hL)
    _ = ∑ P ∈ S, c P.1 Λ * d P.2 Λ * (∑ L ∈ T, pairSectionWeight R a y Λ L P) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = ∑ P ∈ S, c P.1 Λ * d P.2 Λ * (if P.1 = P.2 then (theta a P.1 Λ)⁻¹ else 0) := by
      apply sum_congr rfl
      intro P hP
      obtain ⟨hp, hq⟩ := mem_product.mp hP
      rw [sum_pairSectionWeight_eq hR ha hp hq y hreg Λ hnon]
    _ = _ := by
      dsimp only [S]
      rw [product_eq_sprod, sum_product]
      unfold cM familyMul
      apply sum_congr rfl
      intro P hP
      rw [sum_eq_single P]
      · simp
      · intro Q _ hQ
        simp [Ne.symm hQ]
      · exact fun h => (h hP).elim

end Langlands.GMFamily
