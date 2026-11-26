import Langlands.LinearAlgebra.GMFamilyAffineBases

/-! # Cancellation at a single wall of affine intercepts -/

noncomputable section

open Classical Finset
open scoped BigOperators

namespace Langlands.GMFamily.AffineBases

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι] (v : ι → V)

/-- The sign of a slack, using a fixed regular direction to decide ties. -/
def PositiveSlack (x g : ι → ℝ) (B : BasisIndex v) (j : ι) : Prop :=
  0 < slack v B j x ∨ slack v B j x = 0 ∧ 0 < slack v B j g

/-- The coefficient sum including the tie-breaking convention at singular intercepts. -/
def extendedSum (ℓ : V →ₗ[ℝ] ℂ) (x g : ι → ℝ) : ℂ :=
  ∑ B : BasisIndex v, if ∀ j, j ∉ B.val → PositiveSlack v x g B j then weight v ℓ B else 0

/-- The labels of the inequalities that are tight at a basis intersection. -/
def tight (x : ι → ℝ) (B : BasisIndex v) : Finset ι :=
  univ.filter fun i => slack v B i x = 0

omit [FiniteDimensional ℝ V] in
@[simp] theorem mem_tight (x : ι → ℝ) (B : BasisIndex v) (j : ι) :
    j ∈ tight v x B ↔ slack v B j x = 0 := by
  simp only [tight, mem_filter, mem_univ, true_and]

omit [FiniteDimensional ℝ V] in
private theorem basis_subset_tight (x : ι → ℝ) (B : BasisIndex v) : B.val ⊆ tight v x B := by
  intro i hi
  simp [slack_eq_zero_of_mem v B hi]

omit [FiniteDimensional ℝ V] in
private theorem tight_of_vertex_eq (x : ι → ℝ) {B C : BasisIndex v}
    (h : vertex v C x = vertex v B x) : tight v x C = tight v x B := by
  ext i
  simp [h]

omit [FiniteDimensional ℝ V] in
private theorem vertex_eq_of_subset_tight (x : ι → ℝ) {B C : BasisIndex v}
    (h : C.val ⊆ tight v x B) : vertex v C x = vertex v B x := by
  apply vertex_eq_of_agrees
  intro i hi
  have hi' := (mem_tight v x B i).mp (h hi)
  exact sub_eq_zero.mp hi'

/-- A simple wall point has proportional slack forms among all the vanishing outside
constraints. -/
def SimpleWall (x : ι → ℝ) : Prop :=
  ∀ (B C : BasisIndex v) j k, j ∉ B.val → k ∉ C.val →
    slack v B j x = 0 → slack v C k x = 0 → ∃ a : ℝ, slack v B j = a • slack v C k

/-- Signs of slacks that are already strict at `x` are preserved by the chosen
intercepts and direction. -/
def PreservesStrict (x y g : ι → ℝ) : Prop :=
  ∀ (B : BasisIndex v) j, j ∉ B.val → slack v B j x ≠ 0 →
    (PositiveSlack v y g B j ↔ 0 < slack v B j x)

private theorem tight_eq_or_insert (x : ι → ℝ) (hx : SimpleWall v x) (B : BasisIndex v) :
    tight v x B = B.val ∨ ∃ j ∉ B.val, tight v x B = insert j B.val := by
  by_cases h : ∃ j ∈ tight v x B, j ∉ B.val
  · obtain ⟨j, hjT, hjB⟩ := h
    refine Or.inr ⟨j, hjB, le_antisymm ?_ (insert_subset hjT (basis_subset_tight v x B))⟩
    intro k hk
    by_cases hkB : k ∈ B.val
    · exact mem_insert_of_mem hkB
    · obtain ⟨t, ht⟩ := hx B B k j hkB hjB ((mem_tight v x B k).mp hk) ((mem_tight v x B j).mp hjT)
      exact mem_insert.mpr (Or.inl (eq_of_slack_eq_smul v B hkB hjB t ht))
  · refine Or.inl (le_antisymm ?_ (basis_subset_tight v x B))
    intro k hk
    by_contra hk'
    exact h ⟨k, hk, hk'⟩

private theorem exists_erase_of_tight_augmented (x : ι → ℝ) (B : BasisIndex v) {j : ι}
    (hj : j ∉ B.val) (hT : tight v x B = insert j B.val) (C : BasisIndex v)
    (hC : tight v x C = tight v x B) :
    ∃ k ∈ insert j B.val, C.val = (insert j B.val).erase k := by
  let T := insert j B.val
  have hsub : C.val ⊆ T := by
    dsimp only [T]
    rw [← hT, ← hC]
    exact basis_subset_tight v x C
  have hcard : C.val.card + 1 = T.card := by
    simp only [T, Finset.card_insert_of_notMem hj, card_basisIndex v]
  have hdiff : (T \ C.val).card = 1 := by rw [Finset.card_sdiff_of_subset hsub]; omega
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hdiff
  have hk' : k ∈ T \ C.val := by rw [hk]; exact mem_singleton_self _
  refine ⟨k, (mem_sdiff.mp hk').1, ?_⟩
  have hle : C.val ⊆ T.erase k := by
    intro i hi
    refine mem_erase.mpr ⟨?_, hsub hi⟩
    rintro rfl
    exact (mem_sdiff.mp hk').2 hi
  apply Finset.eq_of_subset_of_card_le hle
  rw [Finset.card_erase_of_mem (mem_sdiff.mp hk').1]
  omega

private theorem sign_pivot {c x : ℝ} (hc : c ≠ 0) (hx : x ≠ 0) :
    (0 < x) ↔ (if 0 < -c * x then c < 0 else 0 < c) := by
  rcases hc.lt_or_gt with hc | hc <;> rcases hx.lt_or_gt with hx | hx
  · simp only [hx.not_gt, hc.not_gt, (mul_neg_of_pos_of_neg (neg_pos.mpr hc) hx).not_gt, ite_false]
  · simp only [hx, hc, mul_pos (neg_pos.mpr hc) hx, ite_true]
  · simp only [hx.not_gt, hc.not_gt, mul_pos_of_neg_of_neg (neg_neg_of_pos hc) hx, ite_true]
  · simp only [hx, hc, (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hx).not_gt, ite_false]

omit [FiniteDimensional ℝ V] [Fintype ι] in
private theorem pos_exchange (B : BasisIndex v) {j : ι} (hj : j ∉ B.val) {k : ι}
    (hk : k ∈ insert j B.val) {C : BasisIndex v} (hC : C.val = (insert j B.val).erase k)
    (hc : dependence v B j k ≠ 0) {y g : ι → ℝ} (hg : Regular v g) :
    PositiveSlack v y g C k ↔
      if PositiveSlack v y g B j then dependence v B j k < 0 else 0 < dependence v B j k := by
  have h1 := slack_eq_neg_dependence_mul_slack_exchange v B hj hk C hC y
  have h2 := slack_eq_neg_dependence_mul_slack_exchange v B hj hk C hC g
  have hkC : k ∉ C.val := by rw [hC]; exact notMem_erase _ _
  have hgC := hg C k hkC
  by_cases hy : slack v C k y = 0
  · simp only [PositiveSlack, h1, h2, hy, mul_zero, lt_irrefl, true_and, false_or]
    exact sign_pivot hc hgC
  · have hn : -dependence v B j k * slack v C k y ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc) hy
    simp only [PositiveSlack, h1, h2, hy, hn, false_and, or_false]
    exact sign_pivot hc hy

private theorem weight_exchange (ℓ : V →ₗ[ℝ] ℂ) (B : BasisIndex v) {j : ι} (hj : j ∉ B.val)
    {k : ι} (hk : k ∈ insert j B.val) {C : BasisIndex v} (hC : C.val = (insert j B.val).erase k) :
    weight v ℓ C = ((gramVolume (fun i : B.val => v i) : ℂ) *
        ∏ i ∈ univ \ insert j B.val, ℓ (v i)) *
      ((|dependence v B j k| : ℝ) : ℂ) * ℓ (v k) := by
  have he : univ \ (insert j B.val).erase k = insert k (univ \ insert j B.val) := by
    ext i
    simp only [mem_sdiff, mem_univ, true_and, mem_erase, mem_insert]
    by_cases e : i = k
    · simp [e]
    · simp [e]
  have hn : k ∉ univ \ insert j B.val := fun h => (mem_sdiff.mp h).2 hk
  rw [weight, hC, gramVolume_exchange v B hj hk, Complex.ofReal_mul, he, prod_insert hn]
  ring

omit [FiniteDimensional ℝ V] [Fintype ι] in
private theorem sum_sign_dependence_eq (ℓ : V →ₗ[ℝ] ℂ) (B : BasisIndex v) {j : ι}
    (hj : j ∉ B.val) (p q : Prop) :
    (∑ k ∈ (insert j B.val).filter (fun k =>
      if p then dependence v B j k < 0 else 0 < dependence v B j k),
        ((|dependence v B j k| : ℝ) : ℂ) * ℓ (v k)) =
    ∑ k ∈ (insert j B.val).filter (fun k =>
      if q then dependence v B j k < 0 else 0 < dependence v B j k),
        ((|dependence v B j k| : ℝ) : ℂ) * ℓ (v k) := by
  suffices h : (∑ k ∈ (insert j B.val).filter (fun k => dependence v B j k < 0),
      ((|dependence v B j k| : ℝ) : ℂ) * ℓ (v k)) =
      ∑ k ∈ (insert j B.val).filter (fun k => 0 < dependence v B j k),
        ((|dependence v B j k| : ℝ) : ℂ) * ℓ (v k) by
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, h]
  apply sub_eq_zero.mp
  rw [sum_filter, sum_filter, ← sum_sub_distrib]
  have hsum := congrArg ℓ (sum_dependence_smul_eq_zero v B hj)
  simp only [map_sum, map_smul, Complex.real_smul, map_zero] at hsum
  conv_rhs => rw [← neg_zero, ← hsum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro k _
  rcases lt_trichotomy (dependence v B j k) 0 with hneg | hzero | hpos
  · simp [hneg, hneg.le, abs_of_neg hneg]
  · simp [hzero]
  · simp [hpos, hpos.not_gt, abs_of_pos hpos]

private theorem feasible_in_fiber (x : ι → ℝ) (B : BasisIndex v) {j : ι} (_hj : j ∉ B.val)
    (hT : tight v x B = insert j B.val) {k : ι} (_hk : k ∈ insert j B.val) {C : BasisIndex v}
    (hC : C.val = (insert j B.val).erase k) {y g : ι → ℝ} (hpres : PreservesStrict v x y g) :
    (∀ i, i ∉ C.val → PositiveSlack v y g C i) ↔
      (∀ i, i ∉ insert j B.val → 0 < slack v B i x) ∧ PositiveSlack v y g C k := by
  have hv : vertex v C x = vertex v B x := by
    apply vertex_eq_of_subset_tight
    rw [hC, hT]
    exact erase_subset _ _
  have hslack (i : ι) : slack v C i x = slack v B i x := by simp [hv]
  have hnon (i : ι) (hi : i ∉ insert j B.val) : slack v C i x ≠ 0 := by
    rw [hslack]
    intro h
    exact hi (hT ▸ (mem_tight v x B i).mpr h)
  have hkC : k ∉ C.val := by rw [hC]; exact notMem_erase _ _
  constructor
  · intro h
    refine ⟨fun i hi => ?_, h k hkC⟩
    have hiC : i ∉ C.val := fun hiC => hi (erase_subset _ _ (hC ▸ hiC))
    rw [← hslack]
    exact (hpres C i hiC (hnon i hi)).mp (h i hiC)
  · rintro ⟨hout, hpos⟩ i hi
    by_cases hik : i = k
    · rwa [hik]
    · have hiT : i ∉ insert j B.val := fun h => hi (hC ▸ mem_erase.mpr ⟨hik, h⟩)
      exact (hpres C i hi (hnon i hiT)).mpr (by rw [hslack]; exact hout i hiT)

private theorem sum_tight_augmented (ℓ : V →ₗ[ℝ] ℂ) (x : ι → ℝ) (B : BasisIndex v)
    {j : ι} (hj : j ∉ B.val) (hT : tight v x B = insert j B.val) {y g : ι → ℝ}
    (hg : Regular v g) (hpres : PreservesStrict v x y g)
    (hout : ∀ i, i ∉ insert j B.val → 0 < slack v B i x) :
    (∑ C ∈ (univ : Finset (BasisIndex v)).filter (fun C =>
      tight v x C = tight v x B ∧ ∀ i, i ∉ C.val → PositiveSlack v y g C i), weight v ℓ C) =
      ((gramVolume (fun i : B.val => v i) : ℂ) * ∏ i ∈ univ \ insert j B.val, ℓ (v i)) *
        ∑ k ∈ (insert j B.val).filter (fun k =>
          if PositiveSlack v y g B j then dependence v B j k < 0 else 0 < dependence v B j k),
          ((|dependence v B j k| : ℝ) : ℂ) * ℓ (v k) := by
  let T := insert j B.val
  let p (k : ι) := if PositiveSlack v y g B j then dependence v B j k < 0 else 0 < dependence v B j k
  have hnon (k : ι) (hp : p k) : dependence v B j k ≠ 0 := by
    unfold p at hp
    split_ifs at hp with hh
    · exact hp.ne
    · exact hp.ne'
  have hex (k : ι) (hk : k ∈ T.filter p) : ∃ C : BasisIndex v, C.val = T.erase k :=
    (exists_exchange_basis_iff v B hj (mem_filter.mp hk).1).mpr (hnon k (mem_filter.mp hk).2)
  let pick (k : ι) (hk : k ∈ T.filter p) := (hex k hk).choose
  have hval (k : ι) (hk : k ∈ T.filter p) : (pick k hk).val = T.erase k := (hex k hk).choose_spec
  rw [mul_sum]
  symm
  apply sum_bij pick
  · intro k hk
    obtain ⟨hkT, hkp⟩ := mem_filter.mp hk
    have hv : vertex v (pick k hk) x = vertex v B x := by
      apply vertex_eq_of_subset_tight
      rw [hval k hk, hT]
      exact erase_subset _ _
    refine mem_filter.mpr ⟨mem_univ _, tight_of_vertex_eq v x hv, ?_⟩
    refine (feasible_in_fiber v x B hj hT hkT (hval k hk) hpres).mpr ⟨hout, ?_⟩
    exact (pos_exchange v B hj hkT (hval k hk) (hnon k hkp) hg).mpr hkp
  · intro k hk m hm he
    have hmT := (mem_filter.mp hm).1
    have hh : T.erase k = T.erase m := (hval k hk).symm.trans ((congrArg Subtype.val he).trans (hval m hm))
    by_contra hne
    exact notMem_erase _ _ (by rw [hh]; exact mem_erase.mpr ⟨hne, (mem_filter.mp hk).1⟩)
  · intro C hC
    obtain ⟨-, hCt, hCf⟩ := mem_filter.mp hC
    obtain ⟨k, hkT, hCval⟩ := exists_erase_of_tight_augmented v x B hj hT C hCt
    have hkn := (exists_exchange_basis_iff v B hj hkT).mp ⟨C, hCval⟩
    have hkp : p k := (pos_exchange v B hj hkT hCval hkn hg).mp
      ((feasible_in_fiber v x B hj hT hkT hCval hpres).mp hCf).2
    have hkm : k ∈ T.filter p := mem_filter.mpr ⟨hkT, hkp⟩
    exact ⟨k, hkm, Subtype.ext ((hval k hkm).trans hCval.symm)⟩
  · intro k hk
    rw [weight_exchange v ℓ B hj (mem_filter.mp hk).1 (hval k hk)]
    ring

private theorem sum_tight_of_unique (ℓ : V →ₗ[ℝ] ℂ) (x : ι → ℝ) (B : BasisIndex v)
    (hT : tight v x B = B.val) {y z g : ι → ℝ}
    (hy : PreservesStrict v x y g) (hz : PreservesStrict v x z g) :
    (∑ C ∈ (univ : Finset (BasisIndex v)).filter (fun C => tight v x C = tight v x B),
      if ∀ i, i ∉ C.val → PositiveSlack v y g C i then weight v ℓ C else 0) =
    ∑ C ∈ (univ : Finset (BasisIndex v)).filter (fun C => tight v x C = tight v x B),
      if ∀ i, i ∉ C.val → PositiveSlack v z g C i then weight v ℓ C else 0 := by
  apply sum_congr rfl
  intro C hC
  have hCt := (mem_filter.mp hC).2
  have hCB : C.val = B.val := by
    have hsub := basis_subset_tight v x C
    rw [hCt, hT] at hsub
    exact eq_of_subset_of_card_le hsub (by simp only [card_basisIndex v, le_refl])
  have he : (∀ i, i ∉ C.val → PositiveSlack v y g C i) ↔
      ∀ i, i ∉ C.val → PositiveSlack v z g C i := by
    apply forall_congr'
    intro i
    apply imp_congr_right
    intro hi
    have hn : slack v C i x ≠ 0 := by
      intro h
      have ht := (mem_tight v x C i).mpr h
      rw [hCt, hT, ← hCB] at ht
      exact hi ht
    exact (hy C i hi hn).trans (hz C i hi hn).symm
  simp only [he]

private theorem sum_tight_of_augmented_eq (ℓ : V →ₗ[ℝ] ℂ) (x : ι → ℝ) (B : BasisIndex v)
    {j : ι} (hj : j ∉ B.val) (hT : tight v x B = insert j B.val) {y z g : ι → ℝ}
    (hg : Regular v g) (hy : PreservesStrict v x y g) (hz : PreservesStrict v x z g) :
    (∑ C ∈ (univ : Finset (BasisIndex v)).filter (fun C => tight v x C = tight v x B),
      if ∀ i, i ∉ C.val → PositiveSlack v y g C i then weight v ℓ C else 0) =
    ∑ C ∈ (univ : Finset (BasisIndex v)).filter (fun C => tight v x C = tight v x B),
      if ∀ i, i ∉ C.val → PositiveSlack v z g C i then weight v ℓ C else 0 := by
  by_cases h : ∀ i, i ∉ insert j B.val → 0 < slack v B i x
  · rw [← sum_filter, ← sum_filter, filter_filter, filter_filter,
      sum_tight_augmented v ℓ x B hj hT hg hy h, sum_tight_augmented v ℓ x B hj hT hg hz h]
    congr 1
    exact sum_sign_dependence_eq v ℓ B hj _ _
  · apply sum_congr rfl
    intro C hC
    have hCt := (mem_filter.mp hC).2
    obtain ⟨k, hk, hCval⟩ := exists_erase_of_tight_augmented v x B hj hT C hCt
    have hny := fun hp => h ((feasible_in_fiber v x B hj hT hk hCval hy).mp hp).1
    have hnz := fun hp => h ((feasible_in_fiber v x B hj hT hk hCval hz).mp hp).1
    simp only [ite_eq_right hny, ite_eq_right hnz]

/-- The coefficient sum agrees on both sides of a simple wall, with arbitrary regular
tie-breaking direction. -/
theorem extendedSum_eq_of_preservesStrict (ℓ : V →ₗ[ℝ] ℂ) {x y z g : ι → ℝ}
    (hx : SimpleWall v x) (hg : Regular v g) (hy : PreservesStrict v x y g)
    (hz : PreservesStrict v x z g) : extendedSum v ℓ y g = extendedSum v ℓ z g := by
  let t := (univ : Finset ι).powerset
  have ht (B : BasisIndex v) (_ : B ∈ (univ : Finset (BasisIndex v))) : tight v x B ∈ t :=
    mem_powerset.mpr (subset_univ _)
  unfold extendedSum
  rw [← sum_fiberwise_of_maps_to ht, ← sum_fiberwise_of_maps_to ht]
  apply sum_congr rfl
  intro s _
  by_cases hs : ((univ : Finset (BasisIndex v)).filter (fun C => tight v x C = s)).Nonempty
  · obtain ⟨B, hB⟩ := hs
    rw [← (mem_filter.mp hB).2]
    rcases tight_eq_or_insert v x hx B with hB' | ⟨j, hj, hT⟩
    · exact sum_tight_of_unique v ℓ x B hB' hy hz
    · exact sum_tight_of_augmented_eq v ℓ x B hj hT hg hy hz
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp

end Langlands.GMFamily.AffineBases
