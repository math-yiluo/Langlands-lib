import Langlands.LinearAlgebra.GMFamilyAffineInvariance
import Langlands.LinearAlgebra.GMFamilySplittingGeometry

/-! # Evaluation at the reference intercepts for a chamber pair -/

noncomputable section

open Classical Finset
open scoped RealInnerProductSpace

namespace Langlands.GMFamily

open AffineBases

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

/-- The index of a simple root in either of the two chambers. -/
abbrev NormalIndices (a : Submodule ℝ E) (P₁ P₂ : Finset E) := simpleRoots a P₁ ⊕ simpleRoots a P₂

/-- The two labelled families of simple normals. -/
def pairedNormals (hR : IsRootSet R) (ha : IsLeviSpace R a) {P₁ P₂ : Finset E}
    (h₁ : P₁ ∈ parabolics R a) (h₂ : P₂ ∈ parabolics R a) :
    NormalIndices a P₁ P₂ → effectiveSpace R a := Sum.elim (simpleNormal hR ha h₁) (simpleNormal hR ha h₂)

private theorem exists_opposite (hR : IsRootSet R) {P₁ P₂ : Finset E}
    (h₁ : P₁ ∈ parabolics R a) (h₂ : P₂ ∈ parabolics R a) (hne : P₁ ≠ P₂) :
    ∃ α ∈ P₁, -α ∈ P₂ := by
  obtain ⟨x, hx, rfl⟩ := (mem_filter.mp h₁).2
  obtain ⟨y, hy, rfl⟩ := (mem_filter.mp h₂).2
  by_contra! h
  apply hne
  ext α
  constructor
  · intro hα
    obtain ⟨hαR, hαx⟩ := mem_filter.mp hα
    have hα₀ : restrictedRoot a α ≠ 0 := fun hzero => hαx.ne'
      ((restrictedRoot_eq_zero_iff_forall_inner a α).mp hzero x hx.1)
    rcases (hy.2 α hαR hα₀).lt_or_gt with hn | hp
    · exact (h α hα (mem_filter.mpr ⟨hR.neg_mem hαR, by rwa [inner_neg_left, neg_pos]⟩)).elim
    · exact mem_filter.mpr ⟨hαR, hp⟩
  · intro hα
    obtain ⟨hαR, hαy⟩ := mem_filter.mp hα
    have hα₀ : restrictedRoot a α ≠ 0 := fun hzero => hαy.ne'
      ((restrictedRoot_eq_zero_iff_forall_inner a α).mp hzero y hy.1)
    rcases (hx.2 α hαR hα₀).lt_or_gt with hn | hp
    · have hneg : -α ∈ posSet R x := mem_filter.mpr ⟨hR.neg_mem hαR, by rwa [inner_neg_left, neg_pos]⟩
      exact (h (-α) hneg (by simpa only [neg_neg] using hα)).elim
    · exact mem_filter.mpr ⟨hαR, hp⟩

private theorem pos_root_eval (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) (f : Module.Dual ℝ (effectiveSpace R a))
    (hf : ∀ i : simpleRoots a P, 0 < f (simpleNormal hR ha hP i)) {α : E} (hα : α ∈ P) :
    ∃ z : effectiveSpace R a, (z : E) = (restrictedRoot a α : E) ∧ 0 < f z := by
  obtain ⟨x, hx, hP'⟩ := (mem_filter.mp hP).2
  have hα₀ : restrictedRoot a α ≠ 0 := fun hzero => by
    have ha' : α ∈ posSet R x := hP' ▸ hα
    exact (mem_filter.mp ha').2.ne' ((restrictedRoot_eq_zero_iff_forall_inner a α).mp hzero x hx.1)
  obtain ⟨c, hc⟩ := exists_sum_simpleRoots hP (mem_image_of_mem (restrictedRoot a) hα)
  let z := ∑ i, c i • simpleNormal hR ha hP i
  refine ⟨z, ?_, ?_⟩
  · have he := congrArg (fun y : a => (y : E)) hc
    change (∑ i, c i • simpleNormal hR ha hP i : effectiveSpace R a).val = _
    simpa only [Submodule.coe_sum, ← Nat.cast_smul_eq_nsmul ℝ, Submodule.coe_smul, simpleNormal] using he
  · have hnon : ∃ i, c i ≠ 0 := by
      by_contra! hn
      exact hα₀ (by simpa [hn] using hc.symm)
    obtain ⟨i, hi⟩ := hnon
    simp only [z, map_sum, map_nsmul, nsmul_eq_mul]
    exact sum_pos' (fun j _ => mul_nonneg (by positivity) (hf j).le)
      ⟨i, mem_univ _, mul_pos (by exact_mod_cast (Nat.pos_of_ne_zero hi)) (hf i)⟩

/-- Distinct chambers give a zero coefficient for any regular pair of translated systems. -/
theorem sum_normalizedWeight_eq_zero_of_ne (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P₁ P₂ : Finset E} (h₁ : P₁ ∈ parabolics R a) (h₂ : P₂ ∈ parabolics R a) (hne : P₁ ≠ P₂)
    (ℓ : effectiveSpace R a →ₗ[ℝ] ℂ) (hℓ : ∀ i, ℓ (pairedNormals hR ha h₁ h₂ i) ≠ 0)
    (b : NormalIndices a P₁ P₂ → ℝ) (hb : Regular (pairedNormals hR ha h₁ h₂) b) :
    ∑ B : BasisIndex (pairedNormals hR ha h₁ h₂),
      (if Feasible (pairedNormals hR ha h₁ h₂) B b then normalizedWeight (pairedNormals hR ha h₁ h₂) ℓ B else 0) = 0 := by
  let K := NormalIndices a P₁ P₂
  let v := pairedNormals hR ha h₁ h₂
  let F (i : K) : Module.Dual ℝ (K → ℝ) := LinearMap.proj i
  have hF (i : K) : F i ≠ 0 := by
    intro he
    have he' := congrArg (fun f : Module.Dual ℝ (K → ℝ) => f (fun _ => 1)) he
    simp [F] at he'
  obtain ⟨b', hb', -, hpos, -⟩ := exists_regular_preserving v F hF (fun _ => 1)
  rw [sum_normalizedWeight_eq v ℓ hℓ hb hb']
  apply sum_eq_zero
  intro B _
  have hbad : ¬ Feasible v B b' := by
    intro hB
    let f := vertex v B b'
    have hf (i : K) : 0 < f (v i) := by
      have hi : 0 < b' i := by simpa [F] using hpos i (by simp [F])
      by_cases him : i ∈ B.val
      · have he := vertex_apply_basis v B b' him
        exact he ▸ hi
      · have h := hB i him
        change 0 < f (v i) - b' i at h
        linarith
    obtain ⟨α, hα, hneg⟩ := exists_opposite hR h₁ h₂ hne
    obtain ⟨z, hz, hzpos⟩ := pos_root_eval hR ha h₁ f (fun i => hf (.inl i)) hα
    obtain ⟨w, hw, hwpos⟩ := pos_root_eval hR ha h₂ f (fun i => hf (.inr i)) hneg
    have he : w = -z := by
      apply Subtype.ext
      rw [hw, Submodule.coe_neg, hz]
      change (a.orthogonalProjectionOnto (-α) : E) = -((a.orthogonalProjectionOnto α : a) : E)
      rw [map_neg, Submodule.coe_neg]
    rw [he, map_neg] at hwpos
    linarith
  exact ite_eq_right hbad

/-- For a repeated chamber the left copy of its normals is a basis of the paired system. -/
def leftBasisIndex (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) : BasisIndex (pairedNormals hR ha hP hP) := by
  let s : Finset (NormalIndices a P P) := (univ : Finset (simpleRoots a P)).map Function.Embedding.inl
  have hs : ∀ i : simpleRoots a P, Sum.inl i ∈ s := fun i => mem_map.mpr ⟨i, mem_univ _, rfl⟩
  let e : simpleRoots a P ≃ s := Equiv.ofBijective (fun i => ⟨Sum.inl i, hs i⟩) ⟨
    fun i j h => Sum.inl.inj (congrArg Subtype.val h),
    fun j => by obtain ⟨i, -, hi⟩ := mem_map.mp j.property; exact ⟨i, Subtype.ext hi⟩⟩
  have he : (fun i : s => pairedNormals hR ha hP hP i) ∘ e = simpleNormal hR ha hP := rfl
  refine ⟨s, ?_, ?_⟩
  · rw [← linearIndependent_equiv e, he]
    exact (simpleNormal_basis hR ha hP).1
  · rw [← e.surjective.range_comp, he]
    exact (simpleNormal_basis hR ha hP).2

/-- For a repeated chamber the feasible coefficient sum is the weight of its left basis. -/
theorem sum_normalizedWeight_eq_left (hR : IsRootSet R) (ha : IsLeviSpace R a)
    {P : Finset E} (hP : P ∈ parabolics R a) (ℓ : effectiveSpace R a →ₗ[ℝ] ℂ)
    (hℓ : ∀ i, ℓ (pairedNormals hR ha hP hP i) ≠ 0) (b : NormalIndices a P P → ℝ)
    (hb : Regular (pairedNormals hR ha hP hP) b) :
    ∑ B : BasisIndex (pairedNormals hR ha hP hP),
      (if Feasible (pairedNormals hR ha hP hP) B b then normalizedWeight (pairedNormals hR ha hP hP) ℓ B else 0) =
      normalizedWeight (pairedNormals hR ha hP hP) ℓ (leftBasisIndex hR ha hP) := by
  let K := NormalIndices a P P
  let v := pairedNormals hR ha hP hP
  let C := leftBasisIndex hR ha hP
  let F (i : simpleRoots a P) : Module.Dual ℝ (K → ℝ) := LinearMap.proj (.inl i) - LinearMap.proj (.inr i)
  let b₀ : K → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)
  have hF (i : simpleRoots a P) : F i ≠ 0 := by
    intro he
    have he' := congrArg (fun f : Module.Dual ℝ (K → ℝ) => f b₀) he
    simp [F, b₀] at he'
  obtain ⟨b', hb', -, hpos, -⟩ := exists_regular_preserving v F hF b₀
  have hlt (i : simpleRoots a P) : b' (.inr i) < b' (.inl i) := by
    simpa [F, b₀, sub_pos] using hpos i (by simp [F, b₀])
  have hCl (i : simpleRoots a P) : Sum.inl i ∈ C.val := mem_map.mpr ⟨i, mem_univ _, rfl⟩
  have hCr (i : simpleRoots a P) : Sum.inr i ∉ C.val := by simp [C, leftBasisIndex]
  have hC : Feasible v C b' := by
    intro j hj
    rcases j with i | i
    · exact (hj (hCl i)).elim
    · change 0 < vertex v C b' (v (.inl i)) - b' (.inr i)
      rw [vertex_apply_basis v C b' (hCl i)]
      exact sub_pos.mpr (hlt i)
  have huniq (B : BasisIndex v) (hB : Feasible v B b') : B = C := by
    have hright (i : simpleRoots a P) : Sum.inr i ∉ B.val := by
      intro hmem
      have h := vertex_apply_basis v B b' hmem
      change vertex v B b' (v (.inl i)) = b' (.inr i) at h
      by_cases hi : Sum.inl i ∈ B.val
      · rw [vertex_apply_basis v B b' hi] at h
        exact (hlt i).ne (h.symm)
      · have hn := hB (.inl i) hi
        change 0 < vertex v B b' (v (.inl i)) - b' (.inl i) at hn
        rw [h] at hn
        exact (hlt i).not_ge (sub_pos.mp hn).le
    apply Subtype.ext
    apply eq_of_subset_of_card_le _ (by simp only [card_basisIndex v, le_refl])
    intro i hi
    rcases i with i | i
    · exact hCl i
    · exact (hright i hi).elim
  rw [sum_normalizedWeight_eq v ℓ hℓ hb hb', sum_eq_single C]
  · exact ite_eq_left hC
  · intro B _ hB
    exact ite_eq_right (fun hb'' => hB (huniq B hb''))
  · simp

end Langlands.GMFamily
