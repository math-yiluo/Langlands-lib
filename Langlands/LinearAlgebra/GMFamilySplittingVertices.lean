import Langlands.LinearAlgebra.GMFamilySplittingWeights

/-! # Affine vertices and the two parabolic sections -/

noncomputable section

open Classical Finset
open scoped RealInnerProductSpace

namespace Langlands.GMFamily

open AffineBases

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

/-- Regularity of the points selected by the displacement for complementary Levi spaces. -/
def RegularDisplacement (R : Finset E) (a : Submodule ℝ E) (ξ : E) : Prop :=
  ∀ L₁ ∈ leviSpaces R a, ∀ L₂ ∈ leviSpaces R a, dCoeff R a L₁ L₂ ≠ 0 →
    ∀ x₁ x₂ : E, x₁ ∈ L₁ ⊓ (centralSpace R)ᗮ → x₂ ∈ L₂ ⊓ (centralSpace R)ᗮ →
      (2 : ℝ) • ξ = x₁ - x₂ → IsRegular R L₁ x₁ ∧ IsRegular R L₂ x₂

variable (hR : IsRootSet R) (ha : IsLeviSpace R a) {P₁ P₂ : Finset E}
  (h₁ : P₁ ∈ parabolics R a) (h₂ : P₂ ∈ parabolics R a)

local notation "V" => effectiveSpace R a
local notation "K" => NormalIndices a P₁ P₂
local notation "v" => pairedNormals hR ha h₁ h₂

/-- The intercepts for the two chambers translated by opposite displacements. -/
def splittingIntercepts (ξ : V) : K → ℝ :=
  Sum.elim (fun i => -⟪simpleNormal hR ha h₁ i, ξ⟫) (fun i => ⟪simpleNormal hR ha h₂ i, ξ⟫)

/-- The Riesz vector of the affine intersection. -/
def splittingVertex (ξ : V) (B : BasisIndex v) : V :=
  (InnerProductSpace.toDual ℝ V).symm (vertex v B (splittingIntercepts hR ha h₁ h₂ ξ)).toContinuousLinearMap

/-- The left and right flats defined by this basis of normals. -/
def vertexFlats (B : BasisIndex v) : Submodule ℝ E × Submodule ℝ E :=
  (normalFlat P₁ B.val.toLeft, normalFlat P₂ B.val.toRight)

private def pointInA (x : V) : a := ⟨x, x.property.1⟩

private theorem vertex_eval_eq_inner (ξ : V) (B : BasisIndex v) (j : K) :
    vertex v B (splittingIntercepts hR ha h₁ h₂ ξ) (v j) = ⟪v j, splittingVertex hR ha h₁ h₂ ξ B⟫ := by
  rw [real_inner_comm (splittingVertex hR ha h₁ h₂ ξ B) (v j)]
  rw [splittingVertex, InnerProductSpace.toDual_symm_apply]
  rfl

/-- The left slack is evaluation at the first translated point. -/
theorem slack_inl_eq (ξ : V) (B : BasisIndex v) (i : simpleRoots a P₁) :
    slack v B (.inl i) (splittingIntercepts hR ha h₁ h₂ ξ) =
      ⟪(i : a), pointInA (splittingVertex hR ha h₁ h₂ ξ B + ξ)⟫ := by
  rw [slack_apply, vertex_eval_eq_inner hR ha h₁ h₂]
  change ⟪simpleNormal hR ha h₁ i, splittingVertex hR ha h₁ h₂ ξ B⟫ - (-⟪simpleNormal hR ha h₁ i, ξ⟫) =
    ⟪simpleNormal hR ha h₁ i, splittingVertex hR ha h₁ h₂ ξ B + ξ⟫
  rw [sub_neg_eq_add, inner_add_right]

/-- The right slack is evaluation at the second translated point. -/
theorem slack_inr_eq (ξ : V) (B : BasisIndex v) (i : simpleRoots a P₂) :
    slack v B (.inr i) (splittingIntercepts hR ha h₁ h₂ ξ) =
      ⟪(i : a), pointInA (splittingVertex hR ha h₁ h₂ ξ B - ξ)⟫ := by
  rw [slack_apply, vertex_eval_eq_inner hR ha h₁ h₂]
  change ⟪simpleNormal hR ha h₂ i, splittingVertex hR ha h₁ h₂ ξ B⟫ - ⟪simpleNormal hR ha h₂ i, ξ⟫ =
    ⟪simpleNormal hR ha h₂ i, splittingVertex hR ha h₁ h₂ ξ B - ξ⟫
  rw [inner_sub_right]

/-- The flats of a basis intersection occur in the sum with nonzero determinant. -/
theorem vertexFlats_mem_and_dCoeff (B : BasisIndex v) :
    (vertexFlats hR ha h₁ h₂ B).1 ∈ leviSpaces R a ∧
    (vertexFlats hR ha h₁ h₂ B).2 ∈ leviSpaces R a ∧
    dCoeff R a (vertexFlats hR ha h₁ h₂ B).1 (vertexFlats hR ha h₁ h₂ B).2 ≠ 0 := by
  refine ⟨normalFlat_mem_leviSpaces hR ha h₁ _, normalFlat_mem_leviSpaces hR ha h₂ _, ?_⟩
  apply (disjSum_is_basis_iff hR ha h₁ h₂ _ _).mp
  rw [toLeft_disjSum_toRight]
  exact B.property

/-- The two translated points of the intersection belong to its flats. -/
theorem vertex_points_mem (ξ : V) (B : BasisIndex v) :
    let x := splittingVertex hR ha h₁ h₂ ξ B
    let L := vertexFlats hR ha h₁ h₂ B
    ((x + ξ : V) : E) ∈ L.1 ⊓ (centralSpace R)ᗮ ∧
    ((x - ξ : V) : E) ∈ L.2 ⊓ (centralSpace R)ᗮ ∧
    (2 : ℝ) • (ξ : E) = ((x + ξ : V) : E) - ((x - ξ : V) : E) := by
  dsimp only
  refine ⟨⟨?_, (splittingVertex hR ha h₁ h₂ ξ B + ξ).property.2⟩,
    ⟨?_, (splittingVertex hR ha h₁ h₂ ξ B - ξ).property.2⟩, ?_⟩
  · let y := pointInA (splittingVertex hR ha h₁ h₂ ξ B + ξ)
    change (y : E) ∈ normalFlat P₁ B.val.toLeft
    apply (mem_normalFlat_iff B.val.toLeft y).mpr
    dsimp only [y]
    intro i hi
    rw [← slack_inl_eq hR ha h₁ h₂ ξ B i, slack_eq_zero_of_mem v B (mem_toLeft.mp hi), LinearMap.zero_apply]
  · let y := pointInA (splittingVertex hR ha h₁ h₂ ξ B - ξ)
    change (y : E) ∈ normalFlat P₂ B.val.toRight
    apply (mem_normalFlat_iff B.val.toRight y).mpr
    dsimp only [y]
    intro i hi
    rw [← slack_inr_eq hR ha h₁ h₂ ξ B i, slack_eq_zero_of_mem v B (mem_toRight.mp hi), LinearMap.zero_apply]
  · simp only [Submodule.coe_add, Submodule.coe_sub, two_smul]
    abel

include hR ha in
private theorem nonzero_restrictedRoot_of_notMem {P : Finset E} (hP : P ∈ parabolics R a)
    (I : Finset (simpleRoots a P)) (i : simpleRoots a P) (hi : i ∉ I)
    {α : E} (hα : restrictedRoot a α = (i : a)) : restrictedRoot (normalFlat P I) α ≠ 0 := by
  intro hz
  have hspan : (i : E) ∈ normalSpan P I := by
    rw [← inf_orthogonal_normalFlat I]
    refine ⟨(i : a).property, ?_⟩
    change (i : E) ∈ (normalFlat P I)ᗮ
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [real_inner_comm]
    change ⟪(i : a), (⟨y, hy.1⟩ : a)⟫ = 0
    rw [← hα, inner_restrictedRoot_subtype]
    exact (restrictedRoot_eq_zero_iff_forall_inner (normalFlat P I) α).mp hz y hy
  have hli : LinearIndependent ℝ (fun j : simpleRoots a P => (j : E)) :=
    (linearIndependent_simpleRoots hR ha hP).map' a.subtype (LinearMap.ker_eq_bot.mpr a.injective_subtype)
  apply hli.notMem_span_image (s := (I : Set (simpleRoots a P))) hi
  apply Submodule.span_mono (s := Set.range (fun i : I => ((i : simpleRoots a P) : E))) _ hspan
  rintro _ ⟨j, rfl⟩
  exact ⟨j.val, j.property, rfl⟩

/-- The target regularity condition ensures that the affine intercepts are generic. -/
theorem regular_splittingIntercepts (ξ : V) (hξ : RegularDisplacement R a (ξ : E)) :
    Regular v (splittingIntercepts hR ha h₁ h₂ ξ) := by
  intro B j hj
  let L := vertexFlats hR ha h₁ h₂ B
  let x := splittingVertex hR ha h₁ h₂ ξ B
  obtain ⟨hL₁, hL₂, hd⟩ := vertexFlats_mem_and_dCoeff hR ha h₁ h₂ B
  obtain ⟨hx₁, hx₂, he⟩ := vertex_points_mem hR ha h₁ h₂ ξ B
  have hh := hξ L.1 hL₁ L.2 hL₂ hd ((x + ξ : V) : E) ((x - ξ : V) : E) hx₁ hx₂ he
  rcases j with i | i
  · rw [slack_inl_eq hR ha h₁ h₂]
    obtain ⟨α, hα, hαi⟩ := mem_image.mp (mem_filter.mp i.property).1
    have hαR := mem_powerset.mp (mem_filter.mp h₁).1 hα
    rw [← hαi, inner_restrictedRoot_subtype]
    exact hh.1.2 α hαR (nonzero_restrictedRoot_of_notMem hR ha h₁ _ i (fun h => hj (mem_toLeft.mp h)) hαi)
  · rw [slack_inr_eq hR ha h₁ h₂]
    obtain ⟨α, hα, hαi⟩ := mem_image.mp (mem_filter.mp i.property).1
    have hαR := mem_powerset.mp (mem_filter.mp h₂).1 hα
    rw [← hαi, inner_restrictedRoot_subtype]
    exact hh.2.2 α hαR (nonzero_restrictedRoot_of_notMem hR ha h₂ _ i (fun h => hj (mem_toRight.mp h)) hαi)

/-- The section at an intersection is the pair of positive root sets of its translated points. -/
theorem vertex_section_eq (ξ : V) (B : BasisIndex v) :
    let x := splittingVertex hR ha h₁ h₂ ξ B
    let L := vertexFlats hR ha h₁ h₂ B
    splittingSection R (ξ : E) L.1 L.2 = (posSet R ((x + ξ : V) : E), posSet R ((x - ξ : V) : E)) := by
  dsimp only
  obtain ⟨hL₁, hL₂, hd⟩ := vertexFlats_mem_and_dCoeff hR ha h₁ h₂ B
  obtain ⟨x₁, x₂, -, -, -, hu⟩ := exists_unique_splitting_points hR ha hL₁ hL₂ hd ξ
  obtain ⟨hx₁, hx₂, he⟩ := vertex_points_mem hR ha h₁ h₂ ξ B
  obtain ⟨he₁, he₂⟩ := hu _ _ hx₁ hx₂ he
  refine splittingSection_eq_of_unique hx₁ hx₂ he (fun y₁ y₂ hy₁ hy₂ hy => ?_)
  obtain ⟨hy₁', hy₂'⟩ := hu y₁ y₂ hy₁ hy₂ hy
  exact ⟨hy₁'.trans he₁.symm, hy₂'.trans he₂.symm⟩

/-- A basis intersection is feasible exactly when the section is incident to the two chambers. -/
theorem feasible_iff_section_subset (ξ : V) (hξ : RegularDisplacement R a (ξ : E)) (B : BasisIndex v) :
    let L := vertexFlats hR ha h₁ h₂ B
    Feasible v B (splittingIntercepts hR ha h₁ h₂ ξ) ↔
      (splittingSection R (ξ : E) L.1 L.2).1 ⊆ P₁ ∧ (splittingSection R (ξ : E) L.1 L.2).2 ⊆ P₂ := by
  dsimp only
  rw [vertex_section_eq hR ha h₁ h₂ ξ B]
  let x := splittingVertex hR ha h₁ h₂ ξ B
  let x₁ := pointInA (x + ξ)
  let x₂ := pointInA (x - ξ)
  have hnon (j : K) (hB : Feasible v B (splittingIntercepts hR ha h₁ h₂ ξ)) :
      0 ≤ slack v B j (splittingIntercepts hR ha h₁ h₂ ξ) := by
    by_cases hj : j ∈ B.val
    · rw [slack_eq_zero_of_mem v B hj, LinearMap.zero_apply]
    · exact (hB j hj).le
  constructor
  · intro hB
    have hnon₁ (i : simpleRoots a P₁) : 0 ≤ ⟪(i : a), x₁⟫ := by
      rw [← slack_inl_eq hR ha h₁ h₂ ξ B]
      exact hnon (.inl i) hB
    have hnon₂ (i : simpleRoots a P₂) : 0 ≤ ⟪(i : a), x₂⟫ := by
      rw [← slack_inr_eq hR ha h₁ h₂ ξ B]
      exact hnon (.inr i) hB
    exact ⟨(posSet_subset_iff_nonneg hR h₁ x₁).mpr (nonneg_posSet_of_nonneg_simpleRoots h₁ x₁ hnon₁),
      (posSet_subset_iff_nonneg hR h₂ x₂).mpr (nonneg_posSet_of_nonneg_simpleRoots h₂ x₂ hnon₂)⟩
  · rintro ⟨ha₁, ha₂⟩ j hj
    apply lt_of_le_of_ne _ (Ne.symm (regular_splittingIntercepts hR ha h₁ h₂ ξ hξ B j hj))
    rcases j with i | i
    · rw [slack_inl_eq hR ha h₁ h₂]
      obtain ⟨α, hα, hαi⟩ := mem_image.mp (mem_filter.mp i.property).1
      rw [← hαi, inner_restrictedRoot_subtype]
      exact (posSet_subset_iff_nonneg hR h₁ x₁).mp ha₁ α hα
    · rw [slack_inr_eq hR ha h₁ h₂]
      obtain ⟨α, hα, hαi⟩ := mem_image.mp (mem_filter.mp i.property).1
      rw [← hαi, inner_restrictedRoot_subtype]
      exact (posSet_subset_iff_nonneg hR h₂ x₂).mp ha₂ α hα

/-- The two Levi flats determine the basis intersection at regular intercepts. -/
theorem vertexFlats_injective (ξ : V) (hξ : RegularDisplacement R a (ξ : E)) :
    Function.Injective (vertexFlats hR ha h₁ h₂) := by
  intro B C hBC
  let xb := splittingVertex hR ha h₁ h₂ ξ B
  let xc := splittingVertex hR ha h₁ h₂ ξ C
  let L := vertexFlats hR ha h₁ h₂ B
  obtain ⟨hL₁, hL₂, hd⟩ := vertexFlats_mem_and_dCoeff hR ha h₁ h₂ B
  obtain ⟨x₁, x₂, -, -, -, hu⟩ := exists_unique_splitting_points hR ha hL₁ hL₂ hd ξ
  obtain ⟨hB₁, hB₂, hB⟩ := vertex_points_mem hR ha h₁ h₂ ξ B
  obtain ⟨hC₁, hC₂, hC⟩ := vertex_points_mem hR ha h₁ h₂ ξ C
  have hC₁' : ((xc + ξ : V) : E) ∈ L.1 ⊓ (centralSpace R)ᗮ := by
    dsimp only [L]
    rw [hBC]
    exact hC₁
  have hC₂' : ((xc - ξ : V) : E) ∈ L.2 ⊓ (centralSpace R)ᗮ := by
    dsimp only [L]
    rw [hBC]
    exact hC₂
  have hxb := (hu _ _ hB₁ hB₂ hB).1
  have hxc := (hu _ _ hC₁' hC₂' hC).1
  have he : xb = xc := add_right_cancel (Subtype.ext (hxb.trans hxc.symm))
  apply Subtype.ext
  ext j
  have hreg := regular_splittingIntercepts hR ha h₁ h₂ ξ hξ
  have hmem (D : BasisIndex v) : j ∈ D.val ↔ slack v D j (splittingIntercepts hR ha h₁ h₂ ξ) = 0 :=
    ⟨fun h => by rw [slack_eq_zero_of_mem v D h, LinearMap.zero_apply],
      fun e => Classical.byContradiction (fun h : j ∉ D.val => hreg D j h e)⟩
  rw [hmem B, hmem C, slack_apply, slack_apply, vertex_eval_eq_inner hR ha h₁ h₂, vertex_eval_eq_inner hR ha h₁ h₂]
  change (⟪v j, xb⟫ - _ = 0) ↔ (⟪v j, xc⟫ - _ = 0)
  rw [he]

/-- The Levi pairs contributing to an incident chamber pair all occur as feasible bases. -/
theorem exists_feasible_vertex_of_sections (ξ : V) (hξ : RegularDisplacement R a (ξ : E))
    {L₁ L₂ : Submodule ℝ E} (hL₁ : L₁ ∈ leviSpaces R a) (hL₂ : L₂ ∈ leviSpaces R a)
    (hd : dCoeff R a L₁ L₂ ≠ 0)
    (hQ₁ : (splittingSection R (ξ : E) L₁ L₂).1 ⊆ P₁)
    (hQ₂ : (splittingSection R (ξ : E) L₁ L₂).2 ⊆ P₂) :
    ∃ B : BasisIndex v, Feasible v B (splittingIntercepts hR ha h₁ h₂ ξ) ∧
      vertexFlats hR ha h₁ h₂ B = (L₁, L₂) := by
  obtain ⟨x₁, x₂, hx₁, hx₂, he, hu⟩ := exists_unique_splitting_points hR ha hL₁ hL₂ hd ξ
  have hreg := hξ L₁ hL₁ L₂ hL₂ hd x₁ x₂ hx₁ hx₂ he
  obtain ⟨hle₁, hf₁⟩ := (mem_leviSpaces_iff hR ha L₁).mp hL₁
  obtain ⟨hle₂, hf₂⟩ := (mem_leviSpaces_iff hR ha L₂).mp hL₂
  let y₁ : a := ⟨x₁, hle₁ hx₁.1⟩
  let y₂ : a := ⟨x₂, hle₂ hx₂.1⟩
  let I := univ.filter fun i : simpleRoots a P₁ => ⟪(i : a), y₁⟫ = 0
  let J := univ.filter fun i : simpleRoots a P₂ => ⟪(i : a), y₂⟫ = 0
  have hsection := splittingSection_eq_of_unique hx₁ hx₂ he hu
  have hpos₁ : posSet R (y₁ : E) ⊆ P₁ := by rw [hsection] at hQ₁; exact hQ₁
  have hpos₂ : posSet R (y₂ : E) ⊆ P₂ := by rw [hsection] at hQ₂; exact hQ₂
  have hF₁ : normalFlat P₁ I = L₁ :=
    (normalFlat_eq_of_zero_filter hR ha h₁ y₁ hpos₁).trans (hf₁.eq_leviSpaceOf_of_regular hreg.1).symm
  have hF₂ : normalFlat P₂ J = L₂ :=
    (normalFlat_eq_of_zero_filter hR ha h₂ y₂ hpos₂).trans (hf₂.eq_leviSpaceOf_of_regular hreg.2).symm
  let B : BasisIndex v := ⟨I.disjSum J, (disjSum_is_basis_iff hR ha h₁ h₂ I J).mpr (by rwa [hF₁, hF₂])⟩
  have hBF : vertexFlats hR ha h₁ h₂ B = (L₁, L₂) := by
    simp only [B, vertexFlats, toLeft_disjSum, toRight_disjSum, hF₁, hF₂]
  refine ⟨B, (feasible_iff_section_subset hR ha h₁ h₂ ξ hξ B).mpr ?_, hBF⟩
  rw [hBF]
  exact ⟨hQ₁, hQ₂⟩

end Langlands.GMFamily
