import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ExponentDirectSum

/-! # Finite sums of joint generalized eigenvectors with prescribed characters -/

universe u v

set_option autoImplicit false

namespace Langlands.HarishChandraSchwartz

variable {A : Type u} [CommGroup A] {Y : Type v} [AddCommGroup Y] [Module ℂ Y]
  (T : A →* Module.End ℂ Y)

/-- `y` is a finite sum of joint generalized eigenvectors of `T` whose characters lie in
`S`. -/
def IsJointlySupportedIn (S : Set (A → ℂ)) (y : Y) : Prop :=
  ∃ (t : Finset (A → ℂ)) (w : (A → ℂ) → Y),
    (∀ δ ∈ t, δ ∈ S ∧ w δ ∈ jointGenEigenspace T δ) ∧ y = ∑ δ ∈ t, w δ

namespace IsJointlySupportedIn

variable {T} {S S' : Set (A → ℂ)}

theorem zero : IsJointlySupportedIn T S 0 :=
  ⟨∅, fun _ => 0, by simp, by simp⟩

theorem of_mem {δ : A → ℂ} (hδ : δ ∈ S) {y : Y} (hy : y ∈ jointGenEigenspace T δ) :
    IsJointlySupportedIn T S y :=
  ⟨{δ}, fun _ => y, by simp [hδ, hy], by simp⟩

theorem mono (h : S ⊆ S') {y : Y} (hy : IsJointlySupportedIn T S y) :
    IsJointlySupportedIn T S' y := by
  obtain ⟨t, w, hw, rfl⟩ := hy
  exact ⟨t, w, fun δ hδ => ⟨h (hw δ hδ).1, (hw δ hδ).2⟩, rfl⟩

omit [CommGroup A] [Module ℂ Y] in
private theorem sum_pad (t t' : Finset (A → ℂ)) (ht : t ⊆ t') (w : (A → ℂ) → Y) :
    ∑ δ ∈ t', (open Classical in if δ ∈ t then w δ else 0) = ∑ δ ∈ t, w δ := by
  classical
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ht]

theorem add {y z : Y} (hy : IsJointlySupportedIn T S y) (hz : IsJointlySupportedIn T S z) :
    IsJointlySupportedIn T S (y + z) := by
  classical
  obtain ⟨t₁, w₁, hw₁, rfl⟩ := hy
  obtain ⟨t₂, w₂, hw₂, rfl⟩ := hz
  refine ⟨t₁ ∪ t₂, fun δ => (if δ ∈ t₁ then w₁ δ else 0) + (if δ ∈ t₂ then w₂ δ else 0),
    fun δ hδ => ⟨?_, ?_⟩, ?_⟩
  · rcases Finset.mem_union.mp hδ with h | h
    · exact (hw₁ δ h).1
    · exact (hw₂ δ h).1
  · refine Submodule.add_mem _ ?_ ?_
    · split_ifs with h
      · exact (hw₁ δ h).2
      · exact Submodule.zero_mem _
    · split_ifs with h
      · exact (hw₂ δ h).2
      · exact Submodule.zero_mem _
  · rw [Finset.sum_add_distrib, sum_pad t₁ _ Finset.subset_union_left,
      sum_pad t₂ _ Finset.subset_union_right]

theorem smul (c : ℂ) {y : Y} (hy : IsJointlySupportedIn T S y) :
    IsJointlySupportedIn T S (c • y) := by
  obtain ⟨t, w, hw, rfl⟩ := hy
  exact ⟨t, fun δ => c • w δ, fun δ hδ => ⟨(hw δ hδ).1, Submodule.smul_mem _ c (hw δ hδ).2⟩,
    by rw [Finset.smul_sum]⟩

theorem neg {y : Y} (hy : IsJointlySupportedIn T S y) : IsJointlySupportedIn T S (-y) := by
  simpa using hy.smul (-1)

theorem sub {y z : Y} (hy : IsJointlySupportedIn T S y) (hz : IsJointlySupportedIn T S z) :
    IsJointlySupportedIn T S (y - z) := by
  simpa only [sub_eq_add_neg] using hy.add hz.neg

theorem finset_sum {ι : Type*} (s : Finset ι) (f : ι → Y)
    (hf : ∀ i ∈ s, IsJointlySupportedIn T S (f i)) :
    IsJointlySupportedIn T S (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsJointlySupportedIn T S (0 : Y))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A decomposition whose components outside `S` vanish exhibits support in `S`. -/
theorem of_decomposition {t : Finset (A → ℂ)} {w : (A → ℂ) → Y}
    (hw : ∀ δ ∈ t, w δ ∈ jointGenEigenspace T δ) (hzero : ∀ δ ∈ t, δ ∉ S → w δ = 0) :
    IsJointlySupportedIn T S (∑ δ ∈ t, w δ) := by
  classical
  refine ⟨t.filter (· ∈ S), w, fun δ hδ => ⟨(Finset.mem_filter.mp hδ).2,
    hw δ (Finset.mem_filter.mp hδ).1⟩, ?_⟩
  rw [Finset.sum_filter_of_ne]
  intro δ hδ hne
  by_contra hS
  exact hne (hzero δ hδ hS)

end IsJointlySupportedIn

open Classical in
/-- Regroup a finite family of joint generalized eigenvectors by their characters. -/
theorem sum_eq_sum_fiberwise_character {ι : Type*} (s : Finset ι) (f : ι → Y) (δ : ι → A → ℂ)
    (hf : ∀ i ∈ s, f i ∈ jointGenEigenspace T (δ i)) :
    (∀ χ ∈ s.image δ, (∑ i ∈ s with δ i = χ, f i) ∈ jointGenEigenspace T χ) ∧
      ∑ χ ∈ s.image δ, (∑ i ∈ s with δ i = χ, f i) = ∑ i ∈ s, f i := by
  classical
  refine ⟨fun χ _ => Submodule.sum_mem _ fun i hi => ?_,
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem δ hi) f⟩
  obtain ⟨hi, hχ⟩ := Finset.mem_filter.mp hi
  rw [← hχ]
  exact hf i hi

open Classical in
/-- Independence: if a finite sum of joint generalized eigenvectors is supported in `S`,
then the sum of the components with any one character outside `S` vanishes. -/
theorem fiber_sum_eq_zero_of_isJointlySupportedIn {ι : Type*} (s : Finset ι) (f : ι → Y)
    (δ : ι → A → ℂ) (hf : ∀ i ∈ s, f i ∈ jointGenEigenspace T (δ i)) {S : Set (A → ℂ)}
    (hS : IsJointlySupportedIn T S (∑ i ∈ s, f i)) {χ : A → ℂ} (hχ : χ ∉ S) :
    ∑ i ∈ s with δ i = χ, f i = 0 := by
  classical
  obtain ⟨t, w, hw, heq⟩ := hS
  obtain ⟨hmem, hsum⟩ := sum_eq_sum_fiberwise_character T s f δ hf
  let U := s.image δ ∪ t ∪ {χ}
  let a (ξ : A → ℂ) : Y := if ξ ∈ s.image δ then ∑ i ∈ s with δ i = ξ, f i else 0
  let b (ξ : A → ℂ) : Y := if ξ ∈ t then w ξ else 0
  have hab : ∀ ξ ∈ U, a ξ ∈ jointGenEigenspace T ξ ∧ b ξ ∈ jointGenEigenspace T ξ := by
    intro ξ _
    constructor
    · simp only [a]
      split_ifs with h
      · exact hmem ξ h
      · exact Submodule.zero_mem _
    · simp only [b]
      split_ifs with h
      · exact (hw ξ h).2
      · exact Submodule.zero_mem _
  have hsumU : ∑ ξ ∈ U, a ξ = ∑ ξ ∈ U, b ξ := by
    simp only [a, b, Finset.sum_ite_mem]
    rw [Finset.inter_eq_right.mpr (Finset.subset_union_left.trans Finset.subset_union_left),
      Finset.inter_eq_right.mpr (Finset.subset_union_right.trans Finset.subset_union_left), hsum,
      heq]
  have hχU : χ ∈ U := Finset.mem_union_right _ (Finset.mem_singleton_self χ)
  have h := (iSupIndep_iff_finsetSum_eq_imp_eq _).mp (iSupIndep_jointGenEigenspace T) U a b hab
    hsumU χ hχU
  have hb : b χ = 0 := by
    simp only [b]
    split_ifs with ht
    · exact absurd (hw χ ht).1 hχ
    · rfl
  by_cases hχs : χ ∈ s.image δ
  · have ha : a χ = ∑ i ∈ s with δ i = χ, f i := by simp only [a, hχs, ↓reduceIte]
    rw [← ha, h, hb]
  · apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨his, hδi⟩ := Finset.mem_filter.mp hi
    exact absurd (hδi ▸ Finset.mem_image_of_mem δ his) hχs

/-- If every finite joint generalized eigendecomposition of `y` has vanishing components
outside `S`, then any one finite family of joint generalized eigenvectors summing to `y`
exhibits `y` as supported in `S`. -/
theorem isJointlySupportedIn_of_fiberVanishing {S : Set (A → ℂ)} {y : Y}
    (hvan : ∀ (sv : Finset (A → ℂ)) (v : (A → ℂ) → Y),
      (∀ δ ∈ sv, v δ ∈ jointGenEigenspace T δ) → ∑ δ ∈ sv, v δ = y →
        ∀ δ ∈ sv, δ ∉ S → v δ = 0)
    {ι : Type*} (s : Finset ι) (f : ι → Y) (δ : ι → A → ℂ)
    (hf : ∀ i ∈ s, f i ∈ jointGenEigenspace T (δ i)) (hy : y = ∑ i ∈ s, f i) :
    IsJointlySupportedIn T S y := by
  classical
  obtain ⟨hmem, hsum⟩ := sum_eq_sum_fiberwise_character T s f δ hf
  have hy' : y = ∑ χ ∈ s.image δ, ∑ i ∈ s with δ i = χ, f i := by rw [hsum, hy]
  rw [hy']
  refine IsJointlySupportedIn.of_decomposition hmem fun χ hχ hS => ?_
  exact hvan (s.image δ) (fun χ => ∑ i ∈ s with δ i = χ, f i) hmem hy'.symm χ hχ hS

/-- The difference of two finite families of joint generalized eigenvectors, in the
situation of `isJointlySupportedIn_of_fiberVanishing`. -/
theorem isJointlySupportedIn_of_fiberVanishing_sub {S : Set (A → ℂ)} {y : Y}
    (hvan : ∀ (sv : Finset (A → ℂ)) (v : (A → ℂ) → Y),
      (∀ δ ∈ sv, v δ ∈ jointGenEigenspace T δ) → ∑ δ ∈ sv, v δ = y →
        ∀ δ ∈ sv, δ ∉ S → v δ = 0)
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → Y) (f' : κ → Y)
    (δ : ι → A → ℂ) (δ' : κ → A → ℂ)
    (hf : ∀ i ∈ s, f i ∈ jointGenEigenspace T (δ i))
    (hf' : ∀ j ∈ t, f' j ∈ jointGenEigenspace T (δ' j))
    (hy : y = ∑ i ∈ s, f i - ∑ j ∈ t, f' j) :
    IsJointlySupportedIn T S y := by
  classical
  let F : ι ⊕ κ → Y := Sum.elim f (fun j => -f' j)
  let Δ : ι ⊕ κ → A → ℂ := Sum.elim δ δ'
  refine isJointlySupportedIn_of_fiberVanishing T hvan (s.disjSum t) F Δ ?_ ?_
  · intro x hx
    rcases x with i | j
    · exact hf i (Finset.inl_mem_disjSum.mp hx)
    · exact Submodule.neg_mem _ (hf' j (Finset.inr_mem_disjSum.mp hx))
  · rw [Finset.sum_disjSum, hy, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    rfl

end Langlands.HarishChandraSchwartz
