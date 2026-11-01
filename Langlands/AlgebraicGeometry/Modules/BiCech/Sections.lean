import Langlands.AlgebraicGeometry.Modules.BiCech.OneDirection

/-!
# Sections of the bi-Čech complex and their local exactness

Let `f : P ⟶ X`, `g : P ⟶ Y` be morphisms of schemes and `𝒰`, `𝒱` ordered affine covers of `X`
and `Y` (a `BiCover P`). For strictly increasing tuples `s`, `t` of indices of `𝒰`, `𝒱` put
`biOpen s t = f⁻¹(𝒰.inter s) ∩ g⁻¹(𝒱.inter t)`. Over an open `V` of `P`, the families
`c s t ∈ F(biOpen s t ∩ V)` form a double complex with the alternating Čech differentials `δ₁`
(in `s`) and `δ₂` (in `t`); its total complex `TSec n V` has differential
`DT = δ₁ + (-1)^p δ₂` on the `(p, q)`-component, and the restrictions of a section over `V`
give an augmentation `augT`.

If `V ⊆ f⁻¹(𝒰.U a) ∩ g⁻¹(𝒱.U b)`, the augmented total complex is exact: in positive degrees a
cocycle `c` is the differential of `preimT c`, built from the contraction `contr₁` inserting `a`
into `s` and, in the column `p = 0`, from the contraction `contr₂` inserting `b` into `t`; in
degree zero a cocycle is the augmentation of its `((a), (b))`-component.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open CechResolution

/-- Ordered affine covers `𝒰`, `𝒱` of schemes `X`, `Y`, with morphisms `f : P ⟶ X` and
`g : P ⟶ Y`. -/
structure BiCover (P : Scheme.{u}) where
  /-- The first target scheme. -/
  X : Scheme.{u}
  /-- The second target scheme. -/
  Y : Scheme.{u}
  /-- The first morphism. -/
  f : P ⟶ X
  /-- The second morphism. -/
  g : P ⟶ Y
  /-- The ordered affine cover of `X`. -/
  𝒰 : X.OrderedAffineCover
  /-- The ordered affine cover of `Y`. -/
  𝒱 : Y.OrderedAffineCover

variable {P : Scheme.{u}} (𝒲 : BiCover P)

/-- The open `f⁻¹(𝒰.inter s) ∩ g⁻¹(𝒱.inter t)` of `P`. -/
def biOpen {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) : P.Opens :=
  𝒲.f ⁻¹ᵁ 𝒲.𝒰.inter s ⊓ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.inter t

/-- The open `biOpen s t ∩ V`, written as the open whose sections are the sections of
`sheafOn F (biOpen s t)` over `V`. -/
abbrev bo (V : P.Opens) {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) : P.Opens :=
  (biOpen 𝒲 s t).ι ''ᵁ ((biOpen 𝒲 s t).ι ⁻¹ᵁ V)

variable {𝒲}

lemma bo_eq (V : P.Opens) {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    bo 𝒲 V s t = biOpen 𝒲 s t ⊓ V :=
  image_preimage_eq _ _

lemma bo_le (V : P.Opens) {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) : bo 𝒲 V s t ≤ V := by
  rw [bo_eq]
  exact inf_le_right

lemma bo_le_face₁ (V : P.Opens) {p q : ℕ} (s : 𝒲.𝒰.Idx (p + 1)) (t : 𝒲.𝒱.Idx q)
    (j : Fin (p + 2)) : bo 𝒲 V s t ≤ bo 𝒲 V (𝒲.𝒰.face s j) t :=
  image_preimage_mono (inf_le_inf_right _ (𝒲.f.preimage_mono (𝒲.𝒰.inter_le_inter_face s j))) V

lemma bo_le_face₂ (V : P.Opens) {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx (q + 1))
    (j : Fin (q + 2)) : bo 𝒲 V s t ≤ bo 𝒲 V s (𝒲.𝒱.face t j) :=
  image_preimage_mono (inf_le_inf_left _ (𝒲.g.preimage_mono (𝒲.𝒱.inter_le_inter_face t j))) V

/-- If every index of `s'` is an index of `s` or `k`, then `𝒰.inter s ∩ 𝒰.U k ⊆ 𝒰.inter s'`. -/
lemma inter_inf_le {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) {p q : ℕ} {s : 𝒰.Idx p}
    {s' : 𝒰.Idx q} {k : 𝒰.ι} (h : Set.range s'.1 ⊆ insert k (Set.range s.1)) :
    𝒰.inter s ⊓ 𝒰.U k ≤ 𝒰.inter s' :=
  le_iInf fun j => by
    rcases Set.mem_insert_iff.1 (h ⟨j, rfl⟩) with hj | ⟨i, hi⟩
    · rw [hj]
      exact inf_le_right
    · rw [← hi]
      exact inf_le_left.trans (𝒰.inter_le s i)

variable (𝒲)

/-- The family of opens `s ↦ biOpen s t ∩ V` for fixed `t` (a row of the double complex). -/
abbrev rowFam (V : P.Opens) {q : ℕ} (t : 𝒲.𝒱.Idx q) : Fam 𝒲.𝒰 P where
  O _ s := bo 𝒲 V s t
  le_face _ s j := bo_le_face₁ V s t j

/-- The family of opens `t ↦ biOpen s t ∩ V` for fixed `s` (a column of the double complex). -/
abbrev colFam (V : P.Opens) {p : ℕ} (s : 𝒲.𝒰.Idx p) : Fam 𝒲.𝒱 P where
  O _ t := bo 𝒲 V s t
  le_face _ t j := bo_le_face₂ V s t j

variable (F : P.Modules)

/-- The `(p, q)`-term of the double complex of sections over `V`. -/
abbrev B (p q : ℕ) (V : P.Opens) : Type u :=
  ∀ (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), Γ(F, bo 𝒲 V s t)

variable {𝒲 F} {V : P.Opens}

section Double

/-- The alternating Čech differential in the first index. -/
def δ₁ {p q : ℕ} (c : B 𝒲 F p q V) : B 𝒲 F (p + 1) q V := fun s t =>
  δ (G := rowFam 𝒲 V t) (fun s' => c s' t) s

/-- The alternating Čech differential in the second index. -/
def δ₂ {p q : ℕ} (c : B 𝒲 F p q V) : B 𝒲 F p (q + 1) V := fun s t =>
  δ (G := colFam 𝒲 V s) (c s) t

lemma δ₁_apply {p q : ℕ} (c : B 𝒲 F p q V) (s : 𝒲.𝒰.Idx (p + 1)) (t : 𝒲.𝒱.Idx q) :
    δ₁ c s t = ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      rs F (bo_le_face₁ V s t j) (c (𝒲.𝒰.face s j) t) :=
  rfl

lemma δ₂_apply {p q : ℕ} (c : B 𝒲 F p q V) (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx (q + 1)) :
    δ₂ c s t = ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      rs F (bo_le_face₂ V s t j) (c s (𝒲.𝒱.face t j)) :=
  rfl

lemma δ₁_add {p q : ℕ} (c c' : B 𝒲 F p q V) : δ₁ (c + c') = δ₁ c + δ₁ c' := by
  funext s t
  exact congrFun (δ_add (G := rowFam 𝒲 V t) (fun s' => c s' t) (fun s' => c' s' t)) s

lemma δ₁_zsmul {p q : ℕ} (n : ℤ) (c : B 𝒲 F p q V) : δ₁ (n • c) = n • δ₁ c := by
  funext s t
  exact congrFun (δ_zsmul (G := rowFam 𝒲 V t) n (fun s' => c s' t)) s

lemma δ₁_zero {p q : ℕ} : δ₁ (0 : B 𝒲 F p q V) = 0 := by
  funext s t
  exact congrFun (δ_zero (G := rowFam 𝒲 V t)) s

lemma δ₂_add {p q : ℕ} (c c' : B 𝒲 F p q V) : δ₂ (c + c') = δ₂ c + δ₂ c' := by
  funext s t
  exact congrFun (δ_add (G := colFam 𝒲 V s) (c s) (c' s)) t

lemma δ₂_zsmul {p q : ℕ} (n : ℤ) (c : B 𝒲 F p q V) : δ₂ (n • c) = n • δ₂ c := by
  funext s t
  exact congrFun (δ_zsmul (G := colFam 𝒲 V s) n (c s)) t

lemma δ₂_zero {p q : ℕ} : δ₂ (0 : B 𝒲 F p q V) = 0 := by
  funext s t
  exact congrFun (δ_zero (G := colFam 𝒲 V s)) t

lemma δ₁_δ₁ {p q : ℕ} (c : B 𝒲 F p q V) : δ₁ (δ₁ c) = 0 := by
  funext s t
  exact congrFun (δ_δ (G := rowFam 𝒲 V t) (fun s' => c s' t)) s

lemma δ₂_δ₂ {p q : ℕ} (c : B 𝒲 F p q V) : δ₂ (δ₂ c) = 0 := by
  funext s t
  exact congrFun (δ_δ (G := colFam 𝒲 V s) (c s)) t

/-- The two differentials commute. -/
lemma δ₁_δ₂ {p q : ℕ} (c : B 𝒲 F p q V) : δ₁ (δ₂ c) = δ₂ (δ₁ c) := by
  funext s t
  simp only [δ₁_apply, δ₂_apply, map_sum, map_zsmul, rs_rs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    congrArg₂ (· • ·) (mul_comm _ _) rfl

/-- A family in first degree `0` which is a restriction of a family depending only on `t` is
killed by `δ₁`. -/
lemma δ₁_eq_zero_of_const {q : ℕ} (c : B 𝒲 F 0 q V) {U : 𝒲.𝒱.Idx q → P.Opens}
    (x : ∀ t, Γ(F, U t)) (hU : ∀ s t, bo 𝒲 V s t ≤ U t)
    (hc : ∀ s t, c s t = rs F (hU s t) (x t)) : δ₁ c = 0 := by
  funext s t
  rw [δ₁_apply, Fin.sum_univ_two]
  simp only [hc, rs_rs, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul]
  exact add_neg_cancel _

/-- A family in second degree `0` which is a restriction of a family depending only on `s` is
killed by `δ₂`. -/
lemma δ₂_eq_zero_of_const {p : ℕ} (c : B 𝒲 F p 0 V) {U : 𝒲.𝒰.Idx p → P.Opens}
    (x : ∀ s, Γ(F, U s)) (hU : ∀ s t, bo 𝒲 V s t ≤ U s)
    (hc : ∀ s t, c s t = rs F (hU s t) (x s)) : δ₂ c = 0 := by
  funext s t
  rw [δ₂_apply, Fin.sum_univ_two]
  simp only [hc, rs_rs, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul]
  exact add_neg_cancel _

end Double

section Contractions

variable (a : 𝒲.𝒰.ι) (b : 𝒲.𝒱.ι)

lemma insStable_row (hV : V ≤ 𝒲.f ⁻¹ᵁ 𝒲.𝒰.U a) {q : ℕ} (t : 𝒲.𝒱.Idx q) :
    InsStable (rowFam 𝒲 V t) a := by
  intro p s hk
  change bo 𝒲 V s t ≤ bo 𝒲 V (insIdx 𝒲.𝒰 s a hk) t
  rw [bo_eq, bo_eq]
  refine le_inf (le_inf ?_ (inf_le_left.trans inf_le_right)) inf_le_right
  exact (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hV)).trans
    (𝒲.f.preimage_mono (inter_inf_le 𝒲.𝒰 (range_insIdx s a hk).subset))

lemma insStable_col (hV : V ≤ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.U b) {p : ℕ} (s : 𝒲.𝒰.Idx p) :
    InsStable (colFam 𝒲 V s) b := by
  intro q t hk
  change bo 𝒲 V s t ≤ bo 𝒲 V s (insIdx 𝒲.𝒱 t b hk)
  rw [bo_eq, bo_eq]
  refine le_inf (le_inf (inf_le_left.trans inf_le_left) ?_) inf_le_right
  exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans hV)).trans
    (𝒲.g.preimage_mono (inter_inf_le 𝒲.𝒱 (range_insIdx t b hk).subset))

variable {a b} (hV : V ≤ 𝒲.f ⁻¹ᵁ 𝒲.𝒰.U a) (hV' : V ≤ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.U b)

/-- The contraction in the first index, inserting `a`. -/
def contr₁ {p q : ℕ} (c : B 𝒲 F (p + 1) q V) : B 𝒲 F p q V := fun s t =>
  contr (insStable_row a hV t) (fun s' => c s' t) s

/-- The contraction in the second index, inserting `b`. -/
def contr₂ {p q : ℕ} (c : B 𝒲 F p (q + 1) V) : B 𝒲 F p q V := fun s t =>
  contr (insStable_col b hV' s) (c s) t

/-- The projection in first degree `0` onto the `(a)`-row. -/
def proj₁ {q : ℕ} (c : B 𝒲 F 0 q V) : B 𝒲 F 0 q V := fun s t =>
  proj (insStable_row a hV t) (fun s' => c s' t) s

lemma contr₁_of_mem {p q : ℕ} (c : B 𝒲 F (p + 1) q V) {s : 𝒲.𝒰.Idx p} (t : 𝒲.𝒱.Idx q)
    (ha : a ∈ Set.range s.1) : contr₁ hV c s t = 0 :=
  contr_of_mem _ _ ha

lemma contr₁_of_notMem {p q : ℕ} (c : B 𝒲 F (p + 1) q V) {s : 𝒲.𝒰.Idx p} (t : 𝒲.𝒱.Idx q)
    (ha : a ∉ Set.range s.1) :
    contr₁ hV c s t = ((-1 : ℤ) ^ pos s.1 a) •
      rs F (insStable_row a hV t p s ha) (c (insIdx 𝒲.𝒰 s a ha) t) :=
  contr_of_notMem _ _ ha

lemma proj₁_apply {q : ℕ} (c : B 𝒲 F 0 q V) (s : 𝒲.𝒰.Idx 0) (t : 𝒲.𝒱.Idx q) :
    proj₁ hV c s t = rs F (le_single (insStable_row a hV t) s) (c (single a) t) :=
  rfl

lemma contr₁_add {p q : ℕ} (c c' : B 𝒲 F (p + 1) q V) :
    contr₁ hV (c + c') = contr₁ hV c + contr₁ hV c' := by
  funext s t
  exact congrFun (contr_add (insStable_row a hV t) (fun s' => c s' t) (fun s' => c' s' t)) s

lemma contr₁_zsmul {p q : ℕ} (n : ℤ) (c : B 𝒲 F (p + 1) q V) :
    contr₁ hV (n • c) = n • contr₁ hV c := by
  funext s t
  exact congrFun (contr_zsmul (insStable_row a hV t) n (fun s' => c s' t)) s

lemma contr₁_zero {p q : ℕ} : contr₁ hV (0 : B 𝒲 F (p + 1) q V) = 0 := by
  funext s t
  exact congrFun (contr_zero (insStable_row a hV t)) s

lemma contr₂_zero {p q : ℕ} : contr₂ hV' (0 : B 𝒲 F p (q + 1) V) = 0 := by
  funext s t
  exact congrFun (contr_zero (insStable_col b hV' s)) t

lemma proj₁_add {q : ℕ} (c c' : B 𝒲 F 0 q V) : proj₁ hV (c + c') = proj₁ hV c + proj₁ hV c' := by
  funext s t
  exact congrFun (proj_add (insStable_row a hV t) (fun s' => c s' t) (fun s' => c' s' t)) s

lemma proj₁_zsmul {q : ℕ} (n : ℤ) (c : B 𝒲 F 0 q V) : proj₁ hV (n • c) = n • proj₁ hV c := by
  funext s t
  exact congrFun (proj_zsmul (insStable_row a hV t) n (fun s' => c s' t)) s

lemma proj₁_sub {q : ℕ} (c c' : B 𝒲 F 0 q V) : proj₁ hV (c - c') = proj₁ hV c - proj₁ hV c' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, proj₁_add, ← neg_one_zsmul c', proj₁_zsmul, neg_one_zsmul]

lemma δ₁_contr₁_add {p q : ℕ} (c : B 𝒲 F (p + 1) q V) :
    δ₁ (contr₁ hV c) + contr₁ hV (δ₁ c) = c := by
  funext s t
  exact congrFun (δ_contr_add_contr_δ (insStable_row a hV t) (fun s' => c s' t)) s

lemma contr₁_δ₁_zero {q : ℕ} (c : B 𝒲 F 0 q V) : contr₁ hV (δ₁ c) = c - proj₁ hV c := by
  funext s t
  exact congrFun (contr_δ_zero (insStable_row a hV t) (fun s' => c s' t)) s

lemma δ₂_contr₂_add {p q : ℕ} (c : B 𝒲 F p (q + 1) V) :
    δ₂ (contr₂ hV' c) + contr₂ hV' (δ₂ c) = c := by
  funext s t
  exact congrFun (δ_contr_add_contr_δ (insStable_col b hV' s) (c s)) t

/-- `contr₁` commutes with `δ₂`. -/
lemma contr₁_δ₂ {p q : ℕ} (c : B 𝒲 F (p + 1) q V) : contr₁ hV (δ₂ c) = δ₂ (contr₁ hV c) := by
  funext s t
  by_cases ha : a ∈ Set.range s.1
  · simp only [δ₂_apply, contr₁_of_mem hV _ _ ha, map_zero, smul_zero, Finset.sum_const_zero]
  · simp only [δ₂_apply, contr₁_of_notMem hV _ _ ha, map_sum, map_zsmul, rs_rs,
      Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun j _ => congrArg₂ (· • ·) (mul_comm _ _) rfl

/-- `proj₁` commutes with `δ₂`. -/
lemma proj₁_δ₂ {q : ℕ} (c : B 𝒲 F 0 q V) : proj₁ hV (δ₂ c) = δ₂ (proj₁ hV c) := by
  funext s t
  simp only [proj₁_apply, δ₂_apply, map_sum, map_zsmul, rs_rs]

lemma δ₁_proj₁ {q : ℕ} (c : B 𝒲 F 0 q V) : δ₁ (proj₁ hV c) = 0 :=
  δ₁_eq_zero_of_const _ (U := fun t => bo 𝒲 V (single a) t) (fun t => c (single a) t)
    (fun s t => le_single (insStable_row a hV t) s) fun _ _ => rfl

end Contractions

section Total

variable (𝒲 F)

/-- The degree-`n` term of the total complex of sections over `V`. -/
abbrev TSec (n : ℕ) (V : P.Opens) : Type u := ∀ p q : ℕ, p + q = n → B 𝒲 F p q V

variable {𝒲 F}

/-- The `δ₁`-part of the total differential. -/
def horT {n : ℕ} (c : TSec 𝒲 F n V) : TSec 𝒲 F (n + 1) V
  | 0, _, _ => 0
  | p + 1, q, h => δ₁ (c p q (by omega))

/-- The `δ₂`-part of the total differential. -/
def verT {n : ℕ} (c : TSec 𝒲 F n V) : TSec 𝒲 F (n + 1) V
  | _, 0, _ => 0
  | p, q + 1, h => δ₂ (c p q (by omega))

/-- The total differential `δ₁ + (-1)^p δ₂`. -/
def DT {n : ℕ} (c : TSec 𝒲 F n V) : TSec 𝒲 F (n + 1) V := fun p q h =>
  horT c p q h + ((-1 : ℤ) ^ p) • verT c p q h

lemma DT_zero_succ {n : ℕ} (c : TSec 𝒲 F n V) (q : ℕ) (h : 0 + (q + 1) = n + 1) :
    DT c 0 (q + 1) h = δ₂ (c 0 q (by omega)) := by
  simp only [DT, horT, verT, pow_zero, one_smul, zero_add]

lemma DT_succ_zero {n : ℕ} (c : TSec 𝒲 F n V) (p : ℕ) (h : p + 1 + 0 = n + 1) :
    DT c (p + 1) 0 h = δ₁ (c p 0 (by omega)) := by
  simp only [DT, horT, verT, smul_zero, add_zero]

lemma DT_succ_succ {n : ℕ} (c : TSec 𝒲 F n V) (p q : ℕ) (h : p + 1 + (q + 1) = n + 1) :
    DT c (p + 1) (q + 1) h =
      δ₁ (c p (q + 1) (by omega)) + ((-1 : ℤ) ^ (p + 1)) • δ₂ (c (p + 1) q (by omega)) := by
  simp only [DT, horT, verT]

lemma neg_one_pow_succ_smul {A : Type*} [AddCommGroup A] (p : ℕ) (x : A) :
    ((-1 : ℤ) ^ (p + 1)) • x = -(((-1 : ℤ) ^ p) • x) := by
  rw [pow_succ, mul_neg_one, neg_smul]

theorem DT_DT {n : ℕ} (c : TSec 𝒲 F n V) (p q : ℕ) (h : p + q = n + 1 + 1) :
    DT (DT c) p q h = 0 := by
  rcases p with _ | p <;> rcases q with _ | q
  · omega
  · rw [DT_zero_succ]
    rcases q with _ | q
    · omega
    · rw [DT_zero_succ, δ₂_δ₂]
  · rw [DT_succ_zero]
    rcases p with _ | p
    · omega
    · rw [DT_succ_zero, δ₁_δ₁]
  · rw [DT_succ_succ]
    rcases p with _ | p <;> rcases q with _ | q
    · rw [DT_zero_succ, DT_succ_zero, δ₁_δ₂, neg_one_pow_succ_smul, pow_zero, one_smul,
        add_neg_cancel]
    · rw [DT_zero_succ, DT_succ_succ, δ₁_δ₂, δ₂_add, δ₂_zsmul, δ₂_δ₂, smul_zero, add_zero,
        neg_one_pow_succ_smul, pow_zero, one_smul, add_neg_cancel]
    · rw [DT_succ_succ, DT_succ_zero, δ₁_add, δ₁_zsmul, δ₁_δ₁, δ₁_δ₂,
        neg_one_pow_succ_smul (p + 1), add_neg_cancel_right]
    · rw [DT_succ_succ, DT_succ_succ, δ₁_add, δ₁_zsmul, δ₁_δ₁, δ₁_δ₂, δ₂_add, δ₂_zsmul,
        δ₂_δ₂, smul_zero, add_zero, neg_one_pow_succ_smul (p + 1), add_neg_cancel_right]

/-- The augmentation: restrictions of a section over `V`. -/
def augT (m : Γ(F, V)) : TSec 𝒲 F 0 V := fun _ _ _ s t => rs F (bo_le V s t) m

theorem DT_augT (m : Γ(F, V)) (p q : ℕ) (h : p + q = 0 + 1) :
    DT (augT (𝒲 := 𝒲) m) p q h = 0 := by
  rcases p with _ | p <;> rcases q with _ | q
  · omega
  · rcases q with _ | q
    · rw [DT_zero_succ]
      exact δ₂_eq_zero_of_const _ (U := fun _ => V) (fun _ => m) (fun s t => bo_le V s t)
        fun _ _ => rfl
    · omega
  · rcases p with _ | p
    · rw [DT_succ_zero]
      exact δ₁_eq_zero_of_const _ (U := fun _ => V) (fun _ => m) (fun s t => bo_le V s t)
        fun _ _ => rfl
    · omega
  · omega

end Total

section Exact

variable {a : 𝒲.𝒰.ι} {b : 𝒲.𝒱.ι} (hV : V ≤ 𝒲.f ⁻¹ᵁ 𝒲.𝒰.U a) (hV' : V ≤ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.U b)

/-- The preimage of a cocycle under the total differential, over `V ⊆ f⁻¹(𝒰.U a) ∩ g⁻¹(𝒱.U b)`. -/
def preimT {n : ℕ} (c : TSec 𝒲 F (n + 1) V) : TSec 𝒲 F n V
  | 0, q, _ => contr₁ hV (c 1 q (by omega)) + proj₁ hV (contr₂ hV' (c 0 (q + 1) (by omega)))
  | p + 1, q, _ => contr₁ hV (c (p + 2) q (by omega))

lemma preimT_zero {n : ℕ} (c : TSec 𝒲 F (n + 1) V) (q : ℕ) (h : 0 + q = n) :
    preimT hV hV' c 0 q h =
      contr₁ hV (c 1 q (by omega)) + proj₁ hV (contr₂ hV' (c 0 (q + 1) (by omega))) :=
  rfl

lemma preimT_succ {n : ℕ} (c : TSec 𝒲 F (n + 1) V) (p q : ℕ) (h : p + 1 + q = n) :
    preimT hV hV' c (p + 1) q h = contr₁ hV (c (p + 2) q (by omega)) :=
  rfl

theorem DT_preimT {n : ℕ} (c : TSec 𝒲 F (n + 1) V)
    (hcomp : ∀ p q (h : p + q = n + 1 + 1), DT c p q h = 0) (p q : ℕ) (h : p + q = n + 1) :
    DT (preimT hV hV' c) p q h = c p q h := by
  rcases p with _ | p
  · rcases q with _ | q
    · omega
    · rw [DT_zero_succ, preimT_zero, δ₂_add, ← contr₁_δ₂, ← proj₁_δ₂]
      have h1 := hcomp (0 + 1) (q + 1) (by omega)
      rw [DT_succ_succ, pow_one, neg_one_smul, add_neg_eq_zero] at h1
      have h2 := hcomp 0 (q + 1 + 1) (by omega)
      rw [DT_zero_succ] at h2
      have h3 := δ₂_contr₂_add hV' (c 0 (q + 1) (by omega))
      rw [h2, contr₂_zero, add_zero] at h3
      rw [← h1, contr₁_δ₁_zero, h3, sub_add_cancel]
  · have key : ∀ (hq : p + 1 + q = n + 1),
        δ₁ (contr₁ hV (c (p + 1) q hq)) +
          ((-1 : ℤ) ^ (p + 1)) • verT (preimT hV hV' c) (p + 1) q h = c (p + 1) q h := by
      intro hq
      rcases q with _ | q
      · have h1 := hcomp (p + 1 + 1) 0 (by omega)
        rw [DT_succ_zero] at h1
        have h3 := δ₁_contr₁_add hV (c (p + 1) 0 (by omega))
        rw [h1, contr₁_zero, add_zero] at h3
        simp only [verT, smul_zero, add_zero]
        exact h3
      · have h1 := hcomp (p + 1 + 1) (q + 1) (by omega)
        rw [DT_succ_succ, neg_one_pow_succ_smul (p + 1), add_neg_eq_zero] at h1
        simp only [verT]
        rw [preimT_succ, ← contr₁_δ₂, ← contr₁_zsmul, ← h1]
        exact δ₁_contr₁_add hV _
    change horT (preimT hV hV' c) (p + 1) q h +
      ((-1 : ℤ) ^ (p + 1)) • verT (preimT hV hV' c) (p + 1) q h = c (p + 1) q h
    simp only [horT]
    rcases p with _ | p
    · rw [preimT_zero, δ₁_add, δ₁_proj₁, add_zero]
      exact key (by omega)
    · rw [preimT_succ]
      exact key (by omega)

include hV hV' in
theorem augT_eq_of_DT_eq_zero (c : TSec 𝒲 F 0 V)
    (hc : ∀ p q (h : p + q = 0 + 1), DT c p q h = 0) : ∃ m : Γ(F, V), augT m = c := by
  set c₀ : B 𝒲 F 0 0 V := c 0 0 rfl with hc₀
  have h1 : δ₁ c₀ = 0 := by
    have := hc (0 + 1) 0 rfl
    rwa [DT_succ_zero] at this
  have h2 : δ₂ c₀ = 0 := by
    have := hc 0 (0 + 1) rfl
    rwa [DT_zero_succ] at this
  have hrow : proj₁ hV c₀ = c₀ := by
    have := contr₁_δ₁_zero hV c₀
    rw [h1, contr₁_zero] at this
    exact (sub_eq_zero.1 this.symm).symm
  have hcol : proj (insStable_col b hV' (single a)) (c₀ (single a)) = c₀ (single a) :=
    eq_proj_of_δ_eq_zero _ _ (congrFun h2 (single a))
  have hle : V ≤ bo 𝒲 V (single a) (single b) := by
    rw [bo_eq]
    refine le_inf (le_inf ?_ ?_) le_rfl
    · exact hV.trans (𝒲.f.preimage_mono (le_iInf fun _ => le_rfl))
    · exact hV'.trans (𝒲.g.preimage_mono (le_iInf fun _ => le_rfl))
  refine ⟨rs F hle (c₀ (single a) (single b)), ?_⟩
  funext p q h s t
  obtain rfl : p = 0 := by omega
  obtain rfl : q = 0 := by omega
  change rs F (bo_le V s t) (rs F hle (c₀ (single a) (single b))) = c₀ s t
  rw [← congrFun (congrFun hrow s) t]
  change _ = rs F _ (c₀ (single a) t)
  rw [← congrFun hcol t]
  simp only [proj, rs_rs]

end Exact

end Langlands.AlgebraicGeometry.Modules.BiCech
