import Langlands.Group.TitsApartmentComparison
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-! # The exchange condition and the parabolic lattice of a Tits system -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-! ### Lengths -/

theorem length_le_length_mul_left_add_one {s : W} (hs : s ∈ S) (w : W) :
    length S w ≤ length S (s * w) + 1 := by
  have := length_mul_left_le h.mul_self h.closure_eq hs (s * w)
  rwa [← mul_assoc, h.mul_self s hs, one_mul] at this

/-- The length changes under left multiplication by a simple element
(Bourbaki, *Lie* IV §2.4). -/
theorem length_mul_left_ne {s : W} (hs : s ∈ S) (w : W) :
    length S (s * w) ≠ length S w := by
  intro heq
  obtain ⟨ns, hns⟩ := h.surjective s
  obtain ⟨b, hb, hbn⟩ := h.conj_not_le s hs ns hns
  obtain ⟨nw, hnw⟩ := h.surjective w
  have hssw : s * (s * w) = w := by rw [← mul_assoc, h.mul_self s hs, one_mul]
  have hle₁ : length S w ≤ length S (s * w) := heq.ge
  have hle₂ : length S (s * w) ≤ length S (s * (s * w)) := by rw [hssw]; exact heq.le
  have hinv : ((ns⁻¹ : N) : G) ∈ cell B π s :=
    mem_cell_of_eq (by simp [hns, h.inv_eq hs])
  have h₁ : (ns : G) * b * (ns : G)⁻¹ * nw ∈ cell B π (s * w) :=
    h.mul_mem_cell_of_length_le hs hle₁ (h.conj_mem_cell hs hns hb hbn) (mem_cell_of_eq hnw)
  have h₂ : ((ns⁻¹ : N) : G) * nw ∈ cell B π (s * w) :=
    h.mul_mem_cell_of_length_le hs hle₁ hinv (mem_cell_of_eq hnw)
  have h₃ : (ns : G) * b * (((ns⁻¹ : N) : G) * nw) ∈ cell B π (s * (s * w)) :=
    h.mul_mem_cell_of_length_le hs hle₂ (mul_mem_cell_right (mem_cell_of_eq hns) hb) h₂
  rw [hssw] at h₃
  have heq' : (ns : G) * b * (((ns⁻¹ : N) : G) * nw) = (ns : G) * b * (ns : G)⁻¹ * nw := by
    simp [mul_assoc]
  rw [heq'] at h₃
  have hw : s * w = w := h.eq_of_mem_cell h₁ h₃
  exact h.ne_one s hs (mul_eq_right.mp hw)

/-- Left multiplication by a simple element changes the length by exactly one. -/
theorem length_mul_left_cases {s : W} (hs : s ∈ S) (w : W) :
    length S (s * w) + 1 = length S w ∨ length S (s * w) = length S w + 1 := by
  have h₁ := length_mul_left_le h.mul_self h.closure_eq hs w
  have h₂ := h.length_le_length_mul_left_add_one hs w
  have h₃ := h.length_mul_left_ne hs w
  omega

/-- A simple element has length one. -/
theorem length_eq_one {s : W} (hs : s ∈ S) : length S s = 1 := by
  have h₁ : length S s ≤ 1 := by simpa using length_le [s] (by simpa using hs)
  have h₂ : length S s ≠ 0 := fun h0 =>
    h.ne_one s hs (eq_one_of_length_eq_zero h.mul_self h.closure_eq h0)
  omega

omit h in
theorem length_one : length S (1 : W) = 0 := by
  simpa using length_le (S := S) [] (by simp)

/-! ### Condition (F) and the exchange condition -/

/-- If left multiplication by `s` decreases the length of `v`, some product
of a point of `C(s)` and a point of `C(v)` lies again in `C(v)`. -/
theorem exists_mul_mem_cell_self_of_length_lt {s v : W} (hs : s ∈ S)
    (hlt : length S (s * v) < length S v) :
    ∃ x ∈ cell B π s, ∃ y ∈ cell B π v, x * y ∈ cell B π v := by
  obtain ⟨ns, hns⟩ := h.surjective s
  obtain ⟨b, hb, hbn⟩ := h.conj_not_le s hs ns hns
  obtain ⟨nu, hnu⟩ := h.surjective (s * v)
  have hssv : s * (s * v) = v := by rw [← mul_assoc, h.mul_self s hs, one_mul]
  have hle : length S (s * v) ≤ length S (s * (s * v)) := by rw [hssv]; exact hlt.le
  have hy : (ns : G) * nu ∈ cell B π v := by
    rw [← hssv]
    exact h.mul_mem_cell_of_length_le hs hle (mem_cell_of_eq hns) (mem_cell_of_eq hnu)
  refine ⟨_, h.conj_mem_cell hs hns hb hbn, _, hy, ?_⟩
  have hxy : (ns : G) * b * (ns : G)⁻¹ * ((ns : G) * nu) = (ns : G) * b * nu := by
    simp [mul_assoc]
  rw [hxy, ← hssv]
  exact h.mul_mem_cell_of_length_le hs hle (mul_mem_cell_right (mem_cell_of_eq hns) hb)
    (mem_cell_of_eq hnu)

private theorem mul_mul_eq_of_length_aux {s s' w : W} (hs : s ∈ S) (hs' : s' ∈ S)
    (h₁ : length S (s * w * s') = length S w) (h₂ : length S (s * w) = length S (w * s'))
    (hgt : length S w < length S (s * w)) : s * w * s' = w := by
  have hv : length S (s * (w * s')) < length S (w * s') := by
    rw [← mul_assoc, h₁, ← h₂]
    exact hgt
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_mem_cell_self_of_length_lt hs hv
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := h.mem_cell_mul hy
  have hxy₁ : x * y₁ ∈ cell B π (s * w) := h.mul_mem_cell_of_length_le hs hgt.le hx hy₁
  rw [← mul_assoc] at hxy
  rcases h.mul_mem_cell_simple_right hs' hxy₁ hy₂ with hc | hc
  · have hws : w * s' = s * w := h.eq_of_mem_cell hxy hc
    rw [mul_assoc, hws, ← mul_assoc, h.mul_self s hs, one_mul]
  · have hws : w * s' = s * w * s' := h.eq_of_mem_cell hxy hc
    have hw : w = s * w := mul_right_cancel hws
    exact absurd (mul_eq_right.mp hw.symm) (h.ne_one s hs)

/-- Condition (F) of Bourbaki, *Lie* IV §1.7, for the Weyl group of a Tits
system: if `ℓ(sws') = ℓ(w)` and `ℓ(sw) = ℓ(ws')` then `sws' = w`. -/
theorem mul_mul_eq_of_length {s s' w : W} (hs : s ∈ S) (hs' : s' ∈ S)
    (h₁ : length S (s * w * s') = length S w) (h₂ : length S (s * w) = length S (w * s')) :
    s * w * s' = w := by
  rcases h.length_mul_left_cases hs w with hlt | hgt
  · have hssw : s * (s * w) = w := by rw [← mul_assoc, h.mul_self s hs, one_mul]
    have h₁' : length S (s * (s * w) * s') = length S (s * w) := by rw [hssw, h₂]
    have h₂' : length S (s * (s * w)) = length S (s * w * s') := by rw [hssw, h₁]
    have hgt' : length S (s * w) < length S (s * (s * w)) := by rw [hssw]; omega
    have key := mul_mul_eq_of_length_aux h hs hs' h₁' h₂' hgt'
    rw [hssw] at key
    rw [mul_assoc, key, ← mul_assoc, h.mul_self s hs, one_mul]
  · exact mul_mul_eq_of_length_aux h hs hs' h₁ h₂ (by omega)

/-- The exchange condition (Bourbaki, *Lie* IV §1.6): if `l` is a reduced word
and `ℓ(s w) < ℓ(w)` for its product `w`, then `s w` is the product of `l`
with one letter deleted. -/
theorem exists_eraseIdx_of_length_mul_lt {l : List W} (hl : ∀ x ∈ l, x ∈ S)
    (hred : length S l.prod = l.length) {s : W} (hs : s ∈ S)
    (hlt : length S (s * l.prod) < l.length) :
    ∃ i < l.length, s * l.prod = (l.eraseIdx i).prod := by
  induction l using List.reverseRecOn with
  | nil => simp at hlt
  | append_singleton l' t ih =>
    have hl' : ∀ x ∈ l', x ∈ S := fun x hx => hl x (by simp [hx])
    have ht : t ∈ S := hl t (by simp)
    simp only [List.prod_append, List.prod_singleton, List.length_append,
      List.length_singleton] at hred hlt ⊢
    have hle' : length S l'.prod ≤ l'.length := length_le l' hl'
    have hge' : length S (l'.prod * t) ≤ length S l'.prod + 1 :=
      length_mul_right_le h.mul_self h.closure_eq ht _
    have hred' : length S l'.prod = l'.length := by omega
    by_cases hlt' : length S (s * l'.prod) < l'.length
    · obtain ⟨i, hi, he⟩ := ih hl' hred' hlt'
      refine ⟨i, by omega, ?_⟩
      rw [List.eraseIdx_append_of_lt_length hi, List.prod_append, ← he]
      simp [mul_assoc]
    · refine ⟨l'.length, by omega, ?_⟩
      rw [List.eraseIdx_append_of_length_le le_rfl]
      simp only [Nat.sub_self, List.eraseIdx_cons_zero, List.append_nil]
      have h₃ := h.length_mul_left_cases hs l'.prod
      have h₄ := h.length_mul_left_cases hs (l'.prod * t)
      have hsw' : length S (s * l'.prod) = length S (l'.prod * t) := by omega
      have hsw : length S (s * l'.prod * t) = length S l'.prod := by
        rw [mul_assoc]
        omega
      rw [← mul_assoc]
      exact h.mul_mul_eq_of_length hs ht hsw hsw'

/-- Every word in `S` contains a reduced subword with the same product
(the deletion condition). -/
theorem exists_sublist_reduced (l : List W) (hl : ∀ x ∈ l, x ∈ S) :
    ∃ m : List W, m.Sublist l ∧ m.prod = l.prod ∧ m.length = length S l.prod := by
  induction l with
  | nil => exact ⟨[], List.Sublist.slnil, rfl, by simp [length_one]⟩
  | cons t l ih =>
    have ht : t ∈ S := hl t (by simp)
    obtain ⟨m, hml, hmp, hmlen⟩ := ih (fun x hx => hl x (by simp [hx]))
    have hmS : ∀ x ∈ m, x ∈ S := fun x hx => hl x (List.mem_cons_of_mem _ (hml.subset hx))
    rcases h.length_mul_left_cases ht l.prod with hlt | hgt
    · have hred : length S m.prod = m.length := by rw [hmp, hmlen]
      obtain ⟨i, hi, he⟩ :=
        h.exists_eraseIdx_of_length_mul_lt hmS hred ht (by rw [hmp]; omega)
      refine ⟨m.eraseIdx i, ((List.eraseIdx_sublist m i).trans hml).cons t, ?_, ?_⟩
      · rw [← he, hmp, List.prod_cons]
      · rw [List.length_eraseIdx_of_lt hi, List.prod_cons]
        omega
    · refine ⟨t :: m, hml.cons_cons t, by simp [hmp], ?_⟩
      simp only [List.length_cons, List.prod_cons]
      omega

/-- Every element of `⟨X⟩`, for `X ⊆ S`, has an `S`-reduced word with letters
in `X`. -/
theorem exists_reduced_word_of_mem_closure {X : Set W} (hX : X ⊆ S) {w : W}
    (hw : w ∈ Subgroup.closure X) :
    ∃ m : List W, (∀ x ∈ m, x ∈ X) ∧ m.prod = w ∧ m.length = length S w := by
  obtain ⟨l, hl, rfl⟩ := exists_word_of_mem_closure (fun s hs => h.mul_self s (hX hs)) hw
  obtain ⟨m, hml, hmp, hmlen⟩ := h.exists_sublist_reduced l (fun x hx => hX (hl x hx))
  exact ⟨m, fun x hx => hl x (hml.subset hx), hmp, hmlen⟩

/-- `⟨X⟩ ∩ S = X` for `X ⊆ S` (Bourbaki, *Lie* IV §1.8, Corollary 1). -/
theorem mem_of_mem_closure {X : Set W} (hX : X ⊆ S) {s : W} (hs : s ∈ S)
    (hsX : s ∈ Subgroup.closure X) : s ∈ X := by
  obtain ⟨m, hmX, hmp, hmlen⟩ := h.exists_reduced_word_of_mem_closure hX hsX
  rw [h.length_eq_one hs] at hmlen
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hmlen
  simp only [List.prod_cons, List.prod_nil, mul_one] at hmp
  subst hmp
  exact hmX x (by simp)

/-- Every letter of every reduced word of an element of `⟨X⟩` lies in `X`
(Bourbaki, *Lie* IV §1.8, Proposition 7). -/
theorem forall_mem_of_reduced_of_mem_closure {X : Set W} (hX : X ⊆ S) {m : List W}
    (hm : ∀ x ∈ m, x ∈ S) (hred : length S m.prod = m.length)
    (hw : m.prod ∈ Subgroup.closure X) : ∀ x ∈ m, x ∈ X := by
  induction m with
  | nil => simp
  | cons t m ih =>
    have ht : t ∈ S := hm t (by simp)
    have hmS : ∀ x ∈ m, x ∈ S := fun x hx => hm x (by simp [hx])
    simp only [List.prod_cons, List.length_cons] at hred hw
    have hle : length S m.prod ≤ m.length := length_le m hmS
    have hge := length_mul_left_le h.mul_self h.closure_eq ht m.prod
    have hred' : length S m.prod = m.length := by omega
    have htw : t * (t * m.prod) = m.prod := by rw [← mul_assoc, h.mul_self t ht, one_mul]
    obtain ⟨k, hkX, hkp, hklen⟩ := h.exists_reduced_word_of_mem_closure hX hw
    have hkS : ∀ x ∈ k, x ∈ S := fun x hx => hX (hkX x hx)
    obtain ⟨i, -, he⟩ := h.exists_eraseIdx_of_length_mul_lt hkS (by rw [hkp, hklen]) ht
      (by rw [hkp, htw, hklen, hred]; omega)
    have hmX : m.prod ∈ Subgroup.closure X := by
      rw [← htw, ← hkp, he]
      exact list_prod_mem (fun x hx =>
        Subgroup.subset_closure (hkX x ((List.eraseIdx_sublist k i).subset hx)))
    have htX : t ∈ X := by
      apply h.mem_of_mem_closure hX ht
      have : t = m.prod * (t * m.prod)⁻¹ := by
        rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, h.inv_eq ht]
      rw [this]
      exact Subgroup.mul_mem _ hmX (Subgroup.inv_mem _ hw)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact htX
    · exact ih hmS hred' hmX x hx

/-- Intersections of standard parabolic subgroups of `W`
(Bourbaki, *Lie* IV §1.8, Theorem 2). -/
theorem iInf_closure {ι : Sort*} {X : ι → Set W} (hX : ∀ i, X i ⊆ S) :
    ⨅ i, Subgroup.closure (X i) = Subgroup.closure (⋂ i, X i) := by
  refine le_antisymm ?_ (le_iInf fun i => Subgroup.closure_mono (Set.iInter_subset X i))
  intro w hw
  obtain ⟨m, hmlen, hmS, rfl⟩ := exists_word_length h.mul_self h.closure_eq w
  have hmem : ∀ x ∈ m, x ∈ ⋂ i, X i := fun x hx => Set.mem_iInter.mpr fun i =>
    h.forall_mem_of_reduced_of_mem_closure (hX i) hmS hmlen.symm
      (Subgroup.mem_iInf.mp hw i) x hx
  exact list_prod_mem fun x hx => Subgroup.subset_closure (hmem x hx)

theorem closure_inf_closure {X Y : Set W} (hX : X ⊆ S) (hY : Y ⊆ S) :
    Subgroup.closure X ⊓ Subgroup.closure Y = Subgroup.closure (X ∩ Y) := by
  refine le_antisymm ?_ (le_inf (Subgroup.closure_mono Set.inter_subset_left)
    (Subgroup.closure_mono Set.inter_subset_right))
  rintro w ⟨hwX, hwY⟩
  obtain ⟨m, hmlen, hmS, rfl⟩ := exists_word_length h.mul_self h.closure_eq w
  exact list_prod_mem fun x hx => Subgroup.subset_closure
    ⟨h.forall_mem_of_reduced_of_mem_closure hX hmS hmlen.symm hwX x hx,
      h.forall_mem_of_reduced_of_mem_closure hY hmS hmlen.symm hwY x hx⟩

/-! ### The lattice of standard parabolic subgroups -/

/-- Membership in `B ⟨X⟩ B` is determined by the Bruhat cell. -/
theorem mem_standardParabolic_iff_of_mem_cell {X : Set W} {w : W} {g : G}
    (hg : g ∈ cell B π w) : g ∈ standardParabolic B π X ↔ w ∈ Subgroup.closure X := by
  constructor
  · rintro ⟨w', hw', hg'⟩
    rwa [h.eq_of_mem_cell hg hg']
  · intro hw
    exact ⟨w, hw, hg⟩

/-- `G_X ≤ G_Y` exactly when `X ⊆ Y` (Bourbaki, *Lie* IV §2.5, Theorem 3). -/
theorem standardParabolicSubgroup_le_iff {X Y : Set W} (hX : X ⊆ S) (hY : Y ⊆ S) :
    h.standardParabolicSubgroup hX ≤ h.standardParabolicSubgroup hY ↔ X ⊆ Y := by
  constructor
  · intro hle s hs
    obtain ⟨n, hn⟩ := h.surjective s
    have hnX : (n : G) ∈ h.standardParabolicSubgroup hX :=
      ⟨s, Subgroup.subset_closure hs, mem_cell_of_eq hn⟩
    have hnY := hle hnX
    exact h.mem_of_mem_closure hY (hX hs)
      ((h.mem_standardParabolic_iff_of_mem_cell (mem_cell_of_eq hn)).mp hnY)
  · rintro hXY g ⟨w, hw, hg⟩
    exact ⟨w, Subgroup.closure_mono hXY hw, hg⟩

theorem standardParabolicSubgroup_injective {X Y : Set W} (hX : X ⊆ S) (hY : Y ⊆ S)
    (he : h.standardParabolicSubgroup hX = h.standardParabolicSubgroup hY) : X = Y :=
  subset_antisymm ((h.standardParabolicSubgroup_le_iff hX hY).mp he.le)
    ((h.standardParabolicSubgroup_le_iff hY hX).mp he.ge)

/-- Intersections of standard parabolic subgroups of `G`
(Bourbaki, *Lie* IV §2.5, Theorem 3). -/
theorem iInf_standardParabolicSubgroup {ι : Sort*} {X : ι → Set W} (hX : ∀ i, X i ⊆ S)
    (hI : (⋂ i, X i) ⊆ S) :
    ⨅ i, h.standardParabolicSubgroup (hX i) = h.standardParabolicSubgroup hI := by
  refine le_antisymm ?_ (le_iInf fun i =>
    (h.standardParabolicSubgroup_le_iff hI (hX i)).mpr (Set.iInter_subset X i))
  intro g hg
  obtain ⟨w, hw⟩ := h.exists_mem_cell g
  have hwi : ∀ i, w ∈ Subgroup.closure (X i) := fun i =>
    (h.mem_standardParabolic_iff_of_mem_cell hw).mp (Subgroup.mem_iInf.mp hg i)
  have hwI : w ∈ Subgroup.closure (⋂ i, X i) := by
    rw [← h.iInf_closure hX]
    exact Subgroup.mem_iInf.mpr hwi
  exact ⟨w, hwI, hw⟩

theorem standardParabolicSubgroup_inf {X Y : Set W} (hX : X ⊆ S) (hY : Y ⊆ S) :
    h.standardParabolicSubgroup hX ⊓ h.standardParabolicSubgroup hY =
      h.standardParabolicSubgroup (fun _ hx => hX hx.1 : X ∩ Y ⊆ S) := by
  refine le_antisymm ?_ (le_inf
    ((h.standardParabolicSubgroup_le_iff _ hX).mpr Set.inter_subset_left)
    ((h.standardParabolicSubgroup_le_iff _ hY).mpr Set.inter_subset_right))
  rintro g ⟨hgX, hgY⟩
  obtain ⟨w, hw⟩ := h.exists_mem_cell g
  have hwX := (h.mem_standardParabolic_iff_of_mem_cell hw).mp hgX
  have hwY := (h.mem_standardParabolic_iff_of_mem_cell hw).mp hgY
  refine ⟨w, ?_, hw⟩
  rw [← h.closure_inf_closure hX hY]
  exact ⟨hwX, hwY⟩

/-- The standard parabolic subgroups form an ordered copy of the subsets of
`S`: `X ↦ G_X = B W_X B` is an order isomorphism onto the subgroups of `G`
containing `B` (Bourbaki, *Lie* IV §2.5, Theorem 3). -/
noncomputable def standardParabolicOrderIso :
    {X : Set W // X ⊆ S} ≃o {P : Subgroup G // B ≤ P} where
  toFun X := ⟨h.standardParabolicSubgroup X.2, h.le_of_coe_eq rfl⟩
  invFun P := ⟨(h.exists_eq_standardParabolic P.1 P.2).choose,
    (h.exists_eq_standardParabolic P.1 P.2).choose_spec.1⟩
  left_inv X := by
    have hspec := (h.exists_eq_standardParabolic (h.standardParabolicSubgroup X.2)
      (h.le_of_coe_eq rfl)).choose_spec
    apply Subtype.ext
    exact (h.standardParabolicSubgroup_injective X.2 hspec.1
      (SetLike.coe_injective hspec.2)).symm
  right_inv P := by
    have hspec := (h.exists_eq_standardParabolic P.1 P.2).choose_spec
    apply Subtype.ext
    exact SetLike.coe_injective hspec.2.symm
  map_rel_iff' {X Y} := h.standardParabolicSubgroup_le_iff X.2 Y.2

@[simp] theorem standardParabolicOrderIso_apply (X : {X : Set W // X ⊆ S}) :
    (h.standardParabolicOrderIso X : Subgroup G) = h.standardParabolicSubgroup X.2 :=
  rfl

/-- The type of a parabolic subgroup is well defined (KP Proposition 1.4.5(2)
and Definition 1.4.6): conjugate standard parabolic subgroups have equal
types. -/
theorem eq_of_conjugateSubgroup_eq {X Y : Set W} (hX : X ⊆ S) (hY : Y ⊆ S) (g k : G)
    (he : conjugateSubgroup g (h.standardParabolicSubgroup hX) =
      conjugateSubgroup k (h.standardParabolicSubgroup hY)) : X = Y := by
  have he' : h.standardParabolicSubgroup hY =
      conjugateSubgroup (k⁻¹ * g) (h.standardParabolicSubgroup hX) := by
    rw [conjugateSubgroup_mul, he, ← conjugateSubgroup_mul, inv_mul_cancel,
      conjugateSubgroup_one]
  have hmem := h.mem_of_eq_conjugate (h.le_of_coe_eq rfl) (h.le_of_coe_eq rfl) he'
  have heq : h.standardParabolicSubgroup hX = h.standardParabolicSubgroup hY := by
    have := congrArg (conjugateSubgroup (k⁻¹ * g)⁻¹) he'
    rwa [conjugateSubgroup_eq_self (Subgroup.inv_mem _ hmem), ← conjugateSubgroup_mul,
      inv_mul_cancel, conjugateSubgroup_one, eq_comm] at this
  exact h.standardParabolicSubgroup_injective hX hY heq

end IsTitsSystem

end Langlands.Group
