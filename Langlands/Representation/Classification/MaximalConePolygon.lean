import Langlands.Representation.Classification.MaximalConeStatement
import Langlands.Representation.Classification.ParabolicConeSubgroupProof

/-!
# Polygon comparison for dominance-maximal cones

Block positions in standard GL coordinates, coarsenings, and the comparison of
the concave cone polygon of a finer exponent with the polygon of a coarser cone.
-/

namespace Langlands

open GeneralLinear
open scoped BigOperators

namespace MaximalConePolygon

/-! ## Generic regrouping of finite sums -/

section Generic

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- A sum over a set of indices described through a map regroups along the fibres. -/
theorem sum_filter_comp (q : ι → κ) (Q : κ → Prop) [DecidablePred Q] (f : ι → ℝ) :
    ∑ k ∈ Finset.univ.filter (fun k => Q (q k)), f k =
      ∑ j ∈ Finset.univ.filter Q, ∑ k ∈ Finset.univ.filter (fun k => q k = j), f k := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun k => Q (q k)))
    (t := Finset.univ.filter Q) (g := q) (by intro k hk; simpa using hk)]
  refine Finset.sum_congr rfl fun j hj => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro rfl
    exact ⟨hj, rfl⟩

variable [LinearOrder ι] [LinearOrder κ]

omit [Fintype κ] in
/-- The indices up to `i₀` split into whole earlier fibres and the initial part of
the fibre of `i₀`. -/
theorem sum_filter_le_split (q : ι → κ) (hq : Monotone q) (f : ι → ℝ) (i₀ : ι) :
    ∑ k ∈ Finset.univ.filter (fun k => k ≤ i₀), f k =
      ∑ k ∈ Finset.univ.filter (fun k => q k < q i₀), f k +
        ∑ k ∈ Finset.univ.filter (fun k => q k = q i₀ ∧ k ≤ i₀), f k := by
  rw [← Finset.sum_union]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hk
      rcases (hq hk).lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hk⟩
    · rintro (h | ⟨_, h⟩)
      · exact (hq.reflect_lt h).le
      · exact h
  · rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    exact (ne_of_lt hk) hk'.1

end Generic

/-! ## Prefix sums of vectors on coordinates -/

section Prefix

variable {n : ℕ}

/-- The sum of the coordinates numbered below `m`. -/
def pre (v : Fin n → ℝ) (m : ℕ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.val < m), v x

theorem pre_split (v : Fin n → ℝ) {u w : ℕ} (huw : u ≤ w) :
    pre v w = pre v u +
      ∑ x ∈ Finset.univ.filter (fun x : Fin n => u ≤ x.val ∧ x.val < w), v x := by
  unfold pre
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> first | (exfalso; omega) | simp

/-- A prefix-sum function with nonincreasing increments on `[a, b)` that is
nonnegative at both ends is nonnegative in between. -/
theorem pre_nonneg_of_antitone (d : Fin n → ℝ) {a b : ℕ}
    (hd : ∀ x y : Fin n, a ≤ x.val → x ≤ y → y.val < b → d y ≤ d x)
    (ha : 0 ≤ pre d a) (hb : 0 ≤ pre d b) {m : ℕ} (ham : a ≤ m) (hmb : m ≤ b) :
    0 ≤ pre d m := by
  by_contra hneg
  push Not at hneg
  have h1 := pre_split d ham
  have hlt : ∑ x ∈ Finset.univ.filter (fun x : Fin n => a ≤ x.val ∧ x.val < m), d x <
      ∑ x ∈ Finset.univ.filter (fun x : Fin n => a ≤ x.val ∧ x.val < m), (0 : ℝ) := by
    rw [Finset.sum_const_zero]
    linarith
  obtain ⟨x₀, hx₀, hdx₀⟩ := Finset.exists_lt_of_sum_lt hlt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₀
  have h2 := pre_split d hmb
  have hle : ∑ x ∈ Finset.univ.filter (fun x : Fin n => m ≤ x.val ∧ x.val < b), d x ≤ 0 := by
    refine Finset.sum_nonpos fun y hy => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hxy : x₀ ≤ y := by
      rw [Fin.le_def]
      omega
    exact (hd x₀ y hx₀.1 hxy hy.2).trans hdx₀.le
  linarith

end Prefix

end MaximalConePolygon

namespace GeneralLinear.BlockShape

open MaximalConePolygon

variable {n : ℕ} (B : BlockShape n)

/-! ## Block positions -/

/-- The first coordinate after the blocks numbered below `m`. -/
def startN (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin B.length => k.val < m), B.size k

private theorem sum_castLE_eq_sum_filter {m : ℕ} (f : Fin m → ℕ) (i : Fin m) :
    ∑ k : Fin i.val, f (Fin.castLE i.2.le k) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k.val < i.val), f k := by
  refine Finset.sum_bij (fun k _ => Fin.castLE i.2.le k) ?_ ?_ ?_ ?_
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
    exact k.2
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b.val, hb⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro k _
    rfl

theorem indexEquiv_val (i : Fin B.length) (a : Fin (B.size i)) :
    (B.indexEquiv ⟨i, a⟩ : ℕ) = B.startN i + a := by
  simp only [indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  rw [sum_castLE_eq_sum_filter B.size i]
  rfl

theorem startN_mono {m m' : ℕ} (h : m ≤ m') : B.startN m ≤ B.startN m' := by
  unfold startN
  refine Finset.sum_le_sum_of_subset ?_
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  omega

theorem startN_succ (i : Fin B.length) : B.startN (i.val + 1) = B.startN i + B.size i := by
  unfold startN
  have : Finset.univ.filter (fun k : Fin B.length => k.val < i.val + 1) =
      insert i (Finset.univ.filter (fun k : Fin B.length => k.val < i.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem startN_of_length_le {m : ℕ} (h : B.length ≤ m) : B.startN m = n := by
  unfold startN
  rw [Finset.filter_true_of_mem (fun k _ => lt_of_lt_of_le k.2 h)]
  exact B.sum_eq

theorem startN_le (m : ℕ) : B.startN m ≤ n :=
  (B.startN_mono (le_max_right B.length m)).trans (B.startN_of_length_le (le_max_left _ _)).le

theorem blockIndex_spec (x : Fin n) :
    B.startN (Geometric.blockIndex B x) ≤ x ∧ (x : ℕ) < B.startN (Geometric.blockIndex B x) + B.size (Geometric.blockIndex B x) := by
  have h := B.indexEquiv_val (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2
  have ha := (B.indexEquiv.symm x).2.isLt
  rw [Sigma.eta, Equiv.apply_symm_apply] at h
  unfold Geometric.blockIndex
  omega

theorem lt_startN_iff (x : Fin n) (m : ℕ) :
    (x : ℕ) < B.startN m ↔ (Geometric.blockIndex B x : ℕ) < m := by
  obtain ⟨h1, h2⟩ := B.blockIndex_spec x
  constructor
  · intro hx
    by_contra hm
    push Not at hm
    have := B.startN_mono hm
    omega
  · intro hm
    have := B.startN_mono (show (Geometric.blockIndex B x : ℕ) + 1 ≤ m from hm)
    rw [B.startN_succ] at this
    omega

theorem blockIndex_eq_iff (x : Fin n) (i : Fin B.length) :
    Geometric.blockIndex B x = i ↔ B.startN i ≤ x ∧ (x : ℕ) < B.startN i + B.size i := by
  constructor
  · rintro rfl
    exact B.blockIndex_spec x
  · rintro ⟨h1, h2⟩
    rw [← B.startN_succ] at h2
    have a1 := (B.lt_startN_iff x _).1 h2
    have a2 : ¬ (Geometric.blockIndex B x : ℕ) < i := fun h => by
      have := (B.lt_startN_iff x i).2 h
      omega
    exact Fin.ext (by omega)

/-- Summing a block function over the coordinates of a set of blocks. -/
theorem sum_blockIndex (g : Fin B.length → ℝ) (P : Fin B.length → Prop) [DecidablePred P] :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n => P (Geometric.blockIndex B x)), g (Geometric.blockIndex B x) =
      ∑ k ∈ Finset.univ.filter P, (B.size k : ℝ) * g k := by
  rw [Finset.sum_filter, Finset.sum_filter, ← B.indexEquiv.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Geometric.blockIndex, Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  split_ifs <;> simp

/-! ## Coarsenings -/

variable {B}
variable {C : BlockShape n} {q : Fin B.length → Fin C.length}

theorem startN_coarsen
    (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
    (j : Fin C.length) :
    C.startN j = ∑ i ∈ Finset.univ.filter (fun i => q i < j), B.size i := by
  have key : ∀ (f : Fin B.length → ℕ),
      ∑ k ∈ Finset.univ.filter (fun k => q k < j), f k =
        ∑ j' ∈ Finset.univ.filter (fun j' : Fin C.length => j' < j),
          ∑ k ∈ Finset.univ.filter (fun k => q k = j'), f k := by
    intro f
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun k => q k < j))
      (t := Finset.univ.filter (fun j' : Fin C.length => j' < j)) (g := q)
      (by intro k hk; simpa using hk)]
    refine Finset.sum_congr rfl fun j' hj' => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
    constructor
    · rintro ⟨_, h⟩
      exact h
    · rintro rfl
      exact ⟨hj', rfl⟩
  rw [key]
  unfold startN
  refine Finset.sum_congr ?_ fun j' _ => hsize j'
  ext j'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Fin.lt_def.symm

end GeneralLinear.BlockShape

namespace MaximalConePolygon

variable {n : ℕ}

/-! ## Fibre sums -/

section Fibres

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- A function whose sum over every fibre vanishes has vanishing sum over every
union of fibres. -/
theorem sum_filter_comp_eq_zero (q : ι → κ) (Q : κ → Prop) [DecidablePred Q] (f : ι → ℝ)
    (hf : ∀ j, ∑ k ∈ Finset.univ.filter (fun k => q k = j), f k = 0) :
    ∑ k ∈ Finset.univ.filter (fun k => Q (q k)), f k = 0 := by
  rw [sum_filter_comp q Q f]
  exact Finset.sum_eq_zero fun j _ => hf j

end Fibres

/-- Under the size and total conditions, the residuals of a block vector against
the constant value on each coarse block sum to zero over every coarse block. -/
theorem fibre_residual_eq_zero {B C : BlockShape n} {r : Fin B.length → ℝ}
    {q : Fin B.length → Fin C.length} {t : Fin C.length → ℝ}
    (hsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
    (htot : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => q i = j), r i) = (C.size j : ℝ) * t j)
    (j : Fin C.length) :
    ∑ k ∈ Finset.univ.filter (fun k => q k = j), (r k - (B.size k : ℝ) * t (q k)) = 0 := by
  rw [Finset.sum_sub_distrib, htot j, hsize j, Nat.cast_sum, Finset.sum_mul]
  rw [sub_eq_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  rw [hk]

/-! ## Cones -/

/-- The cone conditions of `GLMaximalConeJacquetQuotientStatement` for a block
vector `r` along `B`, a consecutive coarsening `q : B → C`, and values `t`. -/
structure IsCone (B : BlockShape n) (r : Fin B.length → ℝ) (C : BlockShape n)
    (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ) : Prop where
  mono : Monotone q
  surj : Function.Surjective q
  size_eq : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i
  anti : StrictAnti t
  total : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => q i = j), r i) = (C.size j : ℝ) * t j
  prefix_le : ∀ i, (∑ k ∈ Finset.univ.filter (fun k => q k = q i ∧ k ≤ i),
    (r k - (B.size k : ℝ) * t (q i))) ≤ 0

/-- The prefix polygon of a cone lies above the partial sums of the block vector
at every block boundary. -/
theorem IsCone.sum_le_of_le {B C : BlockShape n} {r : Fin B.length → ℝ}
    {q : Fin B.length → Fin C.length} {t : Fin C.length → ℝ} (hc : IsCone B r C q t)
    (i : Fin B.length) :
    ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), (r k - (B.size k : ℝ) * t (q k)) ≤ 0 := by
  rw [sum_filter_le_split q hc.mono _ i]
  have h1 : ∑ k ∈ Finset.univ.filter (fun k => q k < q i),
      (r k - (B.size k : ℝ) * t (q k)) = 0 :=
    sum_filter_comp_eq_zero q (fun j => j < q i) _
      (fibre_residual_eq_zero hc.size_eq hc.total)
  have h2 : ∑ k ∈ Finset.univ.filter (fun k => q k = q i ∧ k ≤ i),
      (r k - (B.size k : ℝ) * t (q k)) =
      ∑ k ∈ Finset.univ.filter (fun k => q k = q i ∧ k ≤ i),
        (r k - (B.size k : ℝ) * t (q i)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [hk.1]
  rw [h1, h2, zero_add]
  exact hc.prefix_le i

/-- The cone bound holds over every down-closed set of blocks. -/
theorem IsCone.sum_le_of_downClosed {B C : BlockShape n} {r : Fin B.length → ℝ}
    {q : Fin B.length → Fin C.length} {t : Fin C.length → ℝ} (hc : IsCone B r C q t)
    (s : Finset (Fin B.length)) (hs : ∀ k ∈ s, ∀ k', k' ≤ k → k' ∈ s) :
    ∑ k ∈ s, (r k - (B.size k : ℝ) * t (q k)) ≤ 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hs' : s = Finset.univ.filter (fun k => k ≤ s.max' hne) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hk => s.le_max' k hk, fun hk => hs _ (s.max'_mem hne) k hk⟩
  rw [hs']
  exact hc.sum_le_of_le _

/-! ## Prefix sums of block functions -/

theorem pre_blockIndex_eq (B : BlockShape n) (g : Fin B.length → ℝ) (m : ℕ)
    (P : Fin B.length → Prop) [DecidablePred P]
    (hP : ∀ x : Fin n, (x : ℕ) < m ↔ P (Geometric.blockIndex B x)) :
    pre (fun x => g (Geometric.blockIndex B x)) m =
      ∑ k ∈ Finset.univ.filter P, (B.size k : ℝ) * g k := by
  unfold pre
  rw [Finset.filter_congr (fun x _ => hP x)]
  exact B.sum_blockIndex g P

theorem pre_sub (v w : Fin n → ℝ) (m : ℕ) :
    pre (fun x => v x - w x) m = pre v m - pre w m := by
  unfold pre
  exact Finset.sum_sub_distrib ..

theorem pre_of_le (v : Fin n → ℝ) {m : ℕ} (hm : n ≤ m) : pre v m = pre v n := by
  unfold pre
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-! ## The polygon comparison -/

section Comparison

variable {B : BlockShape n} {r : Fin B.length → ℝ}
  {C : BlockShape n} {p : Fin B.length → Fin C.length} {t : Fin C.length → ℝ}
  {C'' : BlockShape n} {q'' : Fin B.length → Fin C''.length} {t'' : Fin C''.length → ℝ}

/-- The difference of the two polygons at the boundaries of a coarse block
decomposition: the first is the polygon of the cone `(C'', q'', t'')` of `r`, the
second the polygon of `(C, p, t)`, whose block totals agree with those of `r`. -/
private theorem knot_le (hp : Monotone p)
    (hpsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => p i = j), B.size i)
    (hptot : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => p i = j), r i) = (C.size j : ℝ) * t j)
    (hc : IsCone B r C'' q'' t'') (m : ℕ) :
    pre (fun x => t (Geometric.blockIndex C x)) (C.startN m) ≤
      pre (fun x => t'' (Geometric.blockIndex C'' x)) (C.startN m) := by
  have hΛ : (fun x => t (Geometric.blockIndex C x)) = fun x => t (p (Geometric.blockIndex B x)) := by
    funext x
    rw [blockIndex_coarsening B C p hp hpsize]
  have hΛ'' : (fun x => t'' (Geometric.blockIndex C'' x)) = fun x => t'' (q'' (Geometric.blockIndex B x)) := by
    funext x
    rw [blockIndex_coarsening B C'' q'' hc.mono hc.size_eq]
  have hP : ∀ x : Fin n, (x : ℕ) < C.startN m ↔ (fun k => (p k : ℕ) < m) (Geometric.blockIndex B x) := by
    intro x
    rw [C.lt_startN_iff, blockIndex_coarsening B C p hp hpsize]
  rw [hΛ, hΛ'', pre_blockIndex_eq B (fun k => t (p k)) _ (fun k => (p k : ℕ) < m) hP,
    pre_blockIndex_eq B (fun k => t'' (q'' k)) _ (fun k => (p k : ℕ) < m) hP]
  have h1 := hc.sum_le_of_downClosed (Finset.univ.filter (fun k => (p k : ℕ) < m)) (by
    intro k hk k' hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_of_le_of_lt (Fin.le_def.mp (hp hk')) hk)
  have h2 : ∑ k ∈ Finset.univ.filter (fun k => (p k : ℕ) < m),
      (r k - (B.size k : ℝ) * t (p k)) = 0 :=
    sum_filter_comp_eq_zero p (fun j => (j : ℕ) < m) _ (fibre_residual_eq_zero hpsize hptot)
  rw [Finset.sum_sub_distrib] at h1 h2
  linarith

/-- The polygon of any cone of `r` weakly dominates the polygon of a coarse
decomposition with the same block totals. -/
theorem pre_le_of_cone (hp : Monotone p)
    (hpsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => p i = j), B.size i)
    (hptot : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => p i = j), r i) = (C.size j : ℝ) * t j)
    (hc : IsCone B r C'' q'' t'') (m : ℕ) :
    pre (fun x => t (Geometric.blockIndex C x)) m ≤ pre (fun x => t'' (Geometric.blockIndex C'' x)) m := by
  set d : Fin n → ℝ := fun x => t'' (Geometric.blockIndex C'' x) - t (Geometric.blockIndex C x) with hd
  suffices h : ∀ m, 0 ≤ pre d m by
    have := h m
    rw [hd, pre_sub] at this
    linarith
  have hknot : ∀ m, 0 ≤ pre d (C.startN m) := by
    intro m
    rw [hd, pre_sub]
    linarith [knot_le hp hpsize hptot hc m]
  intro m
  rcases lt_or_ge m n with hm | hm
  · set j := Geometric.blockIndex C ⟨m, hm⟩
    obtain ⟨hj1, hj2⟩ := C.blockIndex_spec ⟨m, hm⟩
    refine pre_nonneg_of_antitone d (a := C.startN j) (b := C.startN (j.val + 1)) ?_
      (hknot _) (hknot _) hj1 (by rw [C.startN_succ]; exact hj2.le)
    intro x y hx hxy hy
    rw [C.startN_succ] at hy
    have hx' : Geometric.blockIndex C x = j :=
      (C.blockIndex_eq_iff x j).2 ⟨hx, lt_of_le_of_lt (Fin.le_def.mp hxy) hy⟩
    have hy' : Geometric.blockIndex C y = j :=
      (C.blockIndex_eq_iff y j).2 ⟨le_trans hx (Fin.le_def.mp hxy), hy⟩
    simp only [hd, hx', hy']
    have := hc.anti.antitone (Geometric.blockIndex_monotone C'' hxy)
    linarith
  · have h := hknot C.length
    rw [C.startN_of_length_le le_rfl] at h
    rwa [pre_of_le d hm]

/-- The polygon of any cone of `r` has the same total as the coarse polygon. -/
theorem pre_total_eq_of_cone (hp : Monotone p)
    (hpsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => p i = j), B.size i)
    (hptot : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => p i = j), r i) = (C.size j : ℝ) * t j)
    (hc : IsCone B r C'' q'' t'') :
    pre (fun x => t'' (Geometric.blockIndex C'' x)) n = pre (fun x => t (Geometric.blockIndex C x)) n := by
  have hP : ∀ x : Fin n, (x : ℕ) < n ↔ (fun _ : Fin B.length => True) (Geometric.blockIndex B x) :=
    fun x => iff_of_true x.2 trivial
  have hΛ : (fun x => t (Geometric.blockIndex C x)) = fun x => t (p (Geometric.blockIndex B x)) := by
    funext x
    rw [blockIndex_coarsening B C p hp hpsize]
  have hΛ'' : (fun x => t'' (Geometric.blockIndex C'' x)) = fun x => t'' (q'' (Geometric.blockIndex B x)) := by
    funext x
    rw [blockIndex_coarsening B C'' q'' hc.mono hc.size_eq]
  rw [hΛ, hΛ'', pre_blockIndex_eq B (fun k => t (p k)) _ (fun _ : Fin B.length => True) hP,
    pre_blockIndex_eq B (fun k => t'' (q'' k)) _ (fun _ : Fin B.length => True) hP]
  have h1 := sum_filter_comp_eq_zero q'' (fun _ => True) _
    (fibre_residual_eq_zero hc.size_eq hc.total)
  have h2 := sum_filter_comp_eq_zero p (fun _ => True) _
    (fibre_residual_eq_zero hpsize hptot)
  rw [Finset.sum_sub_distrib] at h1 h2
  linarith

/-- A positive partial residual of `r` against the coarse polygon inside one
coarse block makes the polygon of every cone of `r` strictly larger at the end
of the corresponding block. -/
theorem pre_lt_of_cone (hp : Monotone p)
    (hpsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => p i = j), B.size i)
    (hptot : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => p i = j), r i) = (C.size j : ℝ) * t j)
    (hc : IsCone B r C'' q'' t'') (i : Fin B.length)
    (hi : 0 < ∑ k ∈ Finset.univ.filter (fun k => p k = p i ∧ k ≤ i),
      (r k - (B.size k : ℝ) * t (p i))) :
    pre (fun x => t (Geometric.blockIndex C x)) (B.startN (i.val + 1)) <
      pre (fun x => t'' (Geometric.blockIndex C'' x)) (B.startN (i.val + 1)) := by
  have hΛ : (fun x => t (Geometric.blockIndex C x)) = fun x => t (p (Geometric.blockIndex B x)) := by
    funext x
    rw [blockIndex_coarsening B C p hp hpsize]
  have hΛ'' : (fun x => t'' (Geometric.blockIndex C'' x)) = fun x => t'' (q'' (Geometric.blockIndex B x)) := by
    funext x
    rw [blockIndex_coarsening B C'' q'' hc.mono hc.size_eq]
  have hP : ∀ x : Fin n, (x : ℕ) < B.startN (i.val + 1) ↔
      (fun k => k ≤ i) (Geometric.blockIndex B x) := by
    intro x
    rw [B.lt_startN_iff]
    show _ ↔ Geometric.blockIndex B x ≤ i
    rw [Fin.le_def]
    omega
  rw [hΛ, hΛ'', pre_blockIndex_eq B (fun k => t (p k)) _ (fun k => k ≤ i) hP,
    pre_blockIndex_eq B (fun k => t'' (q'' k)) _ (fun k => k ≤ i) hP]
  have h1 := hc.sum_le_of_le i
  have h2 := sum_filter_le_split p hp (fun k => r k - (B.size k : ℝ) * t (p k)) i
  have h3 : ∑ k ∈ Finset.univ.filter (fun k => p k < p i),
      (r k - (B.size k : ℝ) * t (p k)) = 0 :=
    sum_filter_comp_eq_zero p (fun j => j < p i) _ (fibre_residual_eq_zero hpsize hptot)
  have h4 : ∑ k ∈ Finset.univ.filter (fun k => p k = p i ∧ k ≤ i),
      (r k - (B.size k : ℝ) * t (p k)) =
      ∑ k ∈ Finset.univ.filter (fun k => p k = p i ∧ k ≤ i),
        (r k - (B.size k : ℝ) * t (p i)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [hk.1]
  simp only [Finset.sum_sub_distrib] at h1 h2 h3 h4 hi
  linarith

/-- Strict dominance of a cone polygon over a coarse polygon with the same
block totals, from one positive partial residual inside a coarse block. -/
theorem strictlyDominates_of_cone (hp : Monotone p)
    (hpsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => p i = j), B.size i)
    (hptot : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => p i = j), r i) = (C.size j : ℝ) * t j)
    (hc : IsCone B r C'' q'' t'') (i : Fin B.length)
    (hi : 0 < ∑ k ∈ Finset.univ.filter (fun k => p k = p i ∧ k ≤ i),
      (r k - (B.size k : ℝ) * t (p i))) :
    GLBlockPositivePartStrictlyDominates C'' t'' C t := by
  have htot := pre_total_eq_of_cone hp hpsize hptot hc
  have hall : ∀ v : Fin n → ℝ, ∑ x, v x = pre v n := by
    intro v
    unfold pre
    rw [Finset.filter_true_of_mem (fun x _ => x.2)]
  refine ⟨?_, fun k => pre_le_of_cone hp hpsize hptot hc k.val, ?_⟩
  · have h1 := hall (fun x => t'' (Geometric.blockIndex C'' x))
    have h2 := hall (fun x => t (Geometric.blockIndex C x))
    exact h1.trans (htot.trans h2.symm)
  · exact ⟨⟨B.startN (i.val + 1), Nat.lt_succ_of_le (B.startN_le _)⟩,
      pre_lt_of_cone hp hpsize hptot hc i hi⟩

/-- If no cone of `r` strictly dominates the coarse polygon, every partial residual
of `r` inside a coarse block is nonpositive. -/
theorem residual_nonpos_of_not_strictlyDominates (hp : Monotone p)
    (hpsize : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => p i = j), B.size i)
    (hptot : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => p i = j), r i) = (C.size j : ℝ) * t j)
    (hc : IsCone B r C'' q'' t'') (hmax : ¬ GLBlockPositivePartStrictlyDominates C'' t'' C t)
    (i : Fin B.length) :
    ∑ k ∈ Finset.univ.filter (fun k => p k = p i ∧ k ≤ i),
      (r k - (B.size k : ℝ) * t (p i)) ≤ 0 := by
  by_contra h
  exact hmax (strictlyDominates_of_cone hp hpsize hptot hc i (lt_of_not_ge h))

end Comparison

end MaximalConePolygon

end Langlands
