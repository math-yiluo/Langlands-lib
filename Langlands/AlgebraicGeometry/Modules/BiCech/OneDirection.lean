import Langlands.AlgebraicGeometry.Modules.CechResolution.Exact

/-!
# Alternating Čech section complexes of a family of opens

Let `𝒰` be an ordered affine cover of a scheme `X`; only its ordered index type is used here.
Given a scheme `Z`, an `𝒪_Z`-module `F` and a family of opens `O s` of `Z` indexed by strictly
increasing tuples `s` of indices of `𝒰` and antitone for faces, the families of sections
`s ↦ F(O s)` carry the alternating Čech differential `δ`. If the family is stable under
inserting a fixed index `k` (that is `O s ≤ O (s ∪ {k})`), the operator `contr k` of
`CechResolution.contr` is a full contracting homotopy: `δ ∘ contr k + contr k ∘ δ = id` in
positive degrees, and `contr k ∘ δ = id - proj k` in degree zero, where `proj k` restricts the
`(k)`-component.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open CechResolution

variable {Z : Scheme.{u}} (F : Z.Modules)

/-- Restriction of sections of `F` to a smaller open. -/
abbrev rs {U U' : Z.Opens} (h : U' ≤ U) : Γ(F, U) ⟶ Γ(F, U') :=
  F.presheaf.map (homOfLE h).op

variable {F}

lemma rs_rs {U U' U'' : Z.Opens} (h : U' ≤ U) (h' : U'' ≤ U') (x : Γ(F, U)) :
    rs F h' (rs F h x) = rs F (h'.trans h) x := by
  rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  rfl

lemma rs_self {U : Z.Opens} (h : U ≤ U) (x : Γ(F, U)) : rs F h x = x := by
  change F.presheaf.map (homOfLE h).op x = x
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, F.presheaf.map_id]
  rfl

variable {X : Scheme.{u}}

/-- A family of opens of `Z` indexed by strictly increasing tuples of indices of `𝒰`, antitone
for faces. -/
structure Fam (𝒰 : X.OrderedAffineCover) (Z : Scheme.{u}) where
  /-- The open attached to a tuple. -/
  O : (p : ℕ) → 𝒰.Idx p → Z.Opens
  le_face : ∀ (p : ℕ) (t : 𝒰.Idx (p + 1)) (j : Fin (p + 2)), O (p + 1) t ≤ O p (𝒰.face t j)

variable {𝒰 : X.OrderedAffineCover} (F) (G : Fam 𝒰 Z)

/-- Families of sections `s ↦ F(O s)` in degree `p`. -/
abbrev FSec (p : ℕ) : Type u := ∀ s : 𝒰.Idx p, Γ(F, G.O p s)

variable {F G}

lemma rs_congr {p : ℕ} (c : FSec F G p) {s s' : 𝒰.Idx p} (e : s = s') {U : Z.Opens}
    (h : U ≤ G.O p s) (h' : U ≤ G.O p s') : rs F h (c s) = rs F h' (c s') := by
  subst e
  rfl

/-- The alternating Čech differential on families of sections. -/
def δ {p : ℕ} (c : FSec F G p) : FSec F G (p + 1) := fun t =>
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • rs F (G.le_face p t j) (c (𝒰.face t j))

lemma δ_apply {p : ℕ} (c : FSec F G p) (t : 𝒰.Idx (p + 1)) :
    δ c t = ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • rs F (G.le_face p t j) (c (𝒰.face t j)) :=
  rfl

lemma δ_add {p : ℕ} (c c' : FSec F G p) : δ (c + c') = δ c + δ c' := by
  funext t
  simp only [δ, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

lemma δ_zsmul {p : ℕ} (n : ℤ) (c : FSec F G p) : δ (n • c) = n • δ c := by
  funext t
  simp only [δ, Pi.smul_apply, map_zsmul, Finset.smul_sum, smul_smul, mul_comm n]

lemma δ_zero {p : ℕ} : δ (0 : FSec F G p) = 0 := by
  funext t
  simp only [δ, Pi.zero_apply, map_zero, smul_zero, Finset.sum_const_zero]

lemma δ_neg {p : ℕ} (c : FSec F G p) : δ (-c) = -δ c := by
  rw [← neg_one_zsmul c, δ_zsmul, neg_one_zsmul]

lemma δ_sub {p : ℕ} (c c' : FSec F G p) : δ (c - c') = δ c - δ c' := by
  rw [sub_eq_add_neg, δ_add, δ_neg, ← sub_eq_add_neg]

lemma δ_δ {p : ℕ} (c : FSec F G p) : δ (δ c) = 0 := by
  funext u
  simp only [δ, map_sum, map_zsmul, rs_rs, Finset.smul_sum, smul_smul, ← pow_add, Pi.zero_apply]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (p + 3) × Fin (p + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1 (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ (congrArg Prod.fst heq))
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]
      omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (p + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : 𝒰.face (𝒰.face u a) b = 𝒰.face (𝒰.face u b.succ) a' := by
      apply Subtype.ext
      change u.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) =
        u.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ))) =
        -((-1 : ℤ) ^ (((b.succ : Fin (p + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show (b : ℕ) + 1 + (a : ℕ) = ((a : ℕ) + (b : ℕ)) + 1 by ring, pow_succ]
      ring
    rw [hsign, neg_smul]
    exact congrArg Neg.neg (congrArg₂ (· • ·) rfl (rs_congr c hface _ _))

section Contraction

variable (G) (k : 𝒰.ι)

/-- The family is stable under inserting the index `k`. -/
def InsStable : Prop :=
  ∀ (p : ℕ) (s : 𝒰.Idx p) (hk : k ∉ Set.range s.1), G.O p s ≤ G.O (p + 1) (insIdx 𝒰 s k hk)

variable {G k}

lemma le_single (hG : InsStable G k) (s : 𝒰.Idx 0) : G.O 0 s ≤ G.O 0 (single k) := by
  by_cases hk : k ∈ Set.range s.1
  · rw [idx_zero_eq_single hk]
  · refine (hG 0 s hk).trans ((G.le_face 0 _ ((insPos 𝒰 s k).succAbove 0)).trans (le_of_eq ?_))
    rw [face_insIdx_zero]

/-- The contracting homotopy for an `InsStable` family:
`(contr c) s = (-1)^{#{i | s i < k}} c (s ∪ {k})` for `k ∉ s`, and `0` otherwise. -/
def contr (hG : InsStable G k) {p : ℕ} (c : FSec F G (p + 1)) : FSec F G p := fun s =>
  if hk : k ∈ Set.range s.1 then 0 else
    ((-1 : ℤ) ^ pos s.1 k) • rs F (hG p s hk) (c (insIdx 𝒰 s k hk))

/-- The degree-zero projection `c ↦ (s ↦ c (k)|_{O s})`. -/
def proj (hG : InsStable G k) (c : FSec F G 0) : FSec F G 0 := fun s =>
  rs F (le_single hG s) (c (single k))

variable (hG : InsStable G k)

lemma contr_of_mem {p : ℕ} (c : FSec F G (p + 1)) {s : 𝒰.Idx p} (hk : k ∈ Set.range s.1) :
    contr hG c s = 0 := by
  simp [contr, hk]

lemma contr_of_notMem {p : ℕ} (c : FSec F G (p + 1)) {s : 𝒰.Idx p} (hk : k ∉ Set.range s.1) :
    contr hG c s = ((-1 : ℤ) ^ pos s.1 k) • rs F (hG p s hk) (c (insIdx 𝒰 s k hk)) := by
  simp [contr, hk]

lemma contr_add {p : ℕ} (c c' : FSec F G (p + 1)) :
    contr hG (c + c') = contr hG c + contr hG c' := by
  funext s
  by_cases hk : k ∈ Set.range s.1
  · simp [contr, hk]
  · simp only [contr, hk, dite_false, Pi.add_apply, map_add, smul_add]

lemma contr_zsmul {p : ℕ} (n : ℤ) (c : FSec F G (p + 1)) :
    contr hG (n • c) = n • contr hG c := by
  funext s
  by_cases hk : k ∈ Set.range s.1
  · simp [contr, hk]
  · simp only [contr, hk, dite_false, Pi.smul_apply, map_zsmul, smul_smul, mul_comm n]

lemma contr_zero {p : ℕ} : contr hG (0 : FSec F G (p + 1)) = 0 := by
  funext s
  by_cases hk : k ∈ Set.range s.1
  · simp [contr, hk]
  · simp [contr, hk]

lemma proj_add (c c' : FSec F G 0) : proj hG (c + c') = proj hG c + proj hG c' := by
  funext s
  simp only [proj, Pi.add_apply, map_add]

lemma proj_zsmul (n : ℤ) (c : FSec F G 0) : proj hG (n • c) = n • proj hG c := by
  funext s
  simp only [proj, Pi.smul_apply, map_zsmul]

lemma proj_zero : proj hG (0 : FSec F G 0) = 0 := by
  funext s
  simp only [proj, Pi.zero_apply, map_zero]

/-- The contracting homotopy identity in positive degrees. -/
theorem δ_contr_add_contr_δ {p : ℕ} (c : FSec F G (p + 1)) :
    δ (contr hG c) + contr hG (δ c) = c := by
  funext t
  rw [Pi.add_apply]
  by_cases hk : k ∈ Set.range t.1
  · obtain ⟨m, hm⟩ := hk
    rw [contr_of_mem hG _ ⟨m, hm⟩, add_zero, δ_apply, Finset.sum_eq_single m]
    · have hm' : k ∉ Set.range (𝒰.face t m).1 := hm ▸ self_notMem_range_face t m
      rw [contr_of_notMem hG c hm', map_zsmul, rs_rs, smul_smul]
      have hidx : insIdx 𝒰 (𝒰.face t m) k hm' = t := by
        subst hm
        exact insIdx_face_self t m
      have hpos : pos (𝒰.face t m).1 k = m := by
        subst hm
        exact pos_face_self t m
      rw [rs_congr c hidx _ le_rfl, rs_self, hpos, sign_mul_self, one_smul]
    · intro j _ hj
      rw [contr_of_mem hG _ (hm ▸ self_mem_range_face t hj), map_zero, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [contr_of_notMem hG _ hk, δ_apply, δ_apply, map_sum,
      Fin.sum_univ_succAbove _ (insPos 𝒰 t k), smul_add, Finset.smul_sum]
    simp only [map_zsmul, rs_rs, smul_smul]
    rw [rs_congr c (face_insIdx t k hk) _ le_rfl, rs_self]
    have hpos : ((insPos 𝒰 t k : Fin (p + 3)) : ℕ) = pos t.1 k := rfl
    rw [hpos, sign_mul_self, one_smul, add_left_comm, ← Finset.sum_add_distrib,
      Finset.sum_eq_zero, add_zero]
    intro j _
    rw [contr_of_notMem hG c (notMem_range_face hk j), map_zsmul, rs_rs, smul_smul,
      rs_congr c (face_insIdx_succAbove t k hk j).symm _ ((hG (p + 1) t hk).trans
        (G.le_face _ _ _)), ← add_smul]
    have hs := sign_face t k j
    have hsign : (-1 : ℤ) ^ (j : ℕ) * (-1) ^ pos (𝒰.face t j).1 k +
        (-1) ^ pos t.1 k * (-1) ^ ((insPos 𝒰 t k).succAbove j : ℕ) = 0 := by
      rw [← pow_add, ← pow_add, ← hs, pow_succ]
      ring
    rw [hsign, zero_smul]

/-- The contracting homotopy identity in degree zero. -/
theorem contr_δ_zero (c : FSec F G 0) : contr hG (δ c) = c - proj hG c := by
  funext s
  rw [Pi.sub_apply, proj]
  by_cases hk : k ∈ Set.range s.1
  · rw [contr_of_mem hG _ hk, rs_congr c (idx_zero_eq_single hk).symm _ le_rfl, rs_self,
      sub_self]
  · rw [contr_of_notMem hG _ hk, δ_apply, map_sum, Fin.sum_univ_succAbove _ (insPos 𝒰 s k),
      Fin.sum_univ_one, smul_add]
    simp only [map_zsmul, rs_rs, smul_smul]
    rw [rs_congr c (face_insIdx s k hk) _ le_rfl, rs_self,
      rs_congr c (face_insIdx_zero s k hk) _ (le_single hG s)]
    have hpos : ((insPos 𝒰 s k : Fin 2) : ℕ) = pos s.1 k := rfl
    have hm := pos_le s.1 k
    have hsum : pos s.1 k + ((insPos 𝒰 s k).succAbove 0 : ℕ) = 1 := by
      rw [val_succAbove, hpos]
      split_ifs <;> omega
    rw [hpos, sign_mul_self, one_smul, ← pow_add, hsum, pow_one, neg_one_smul, sub_eq_add_neg]

/-- Exactness in positive degrees: a cocycle is the differential of its contraction. -/
theorem δ_contr_of_δ_eq_zero {p : ℕ} (c : FSec F G (p + 1)) (hc : δ c = 0) :
    δ (contr hG c) = c := by
  have h := δ_contr_add_contr_δ hG c
  rwa [hc, contr_zero, add_zero] at h

/-- Exactness in degree zero: a cocycle equals its projection. -/
theorem eq_proj_of_δ_eq_zero (c : FSec F G 0) (hc : δ c = 0) : proj hG c = c := by
  have h := contr_δ_zero hG c
  rw [hc, contr_zero] at h
  exact (sub_eq_zero.1 h.symm).symm

end Contraction

end Langlands.AlgebraicGeometry.Modules.BiCech
