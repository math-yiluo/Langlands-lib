import Langlands.Geometry.Analytic.DrinfeldNearestVertex
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Adapted bases for ultrametric vector norms over a local field -/

noncomputable section

universe v w u

namespace Langlands.Analytic.VectorNorm

open Set

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]

/-- A family is orthogonal if the norm of a linear combination is at least the norm of
any one of its terms. The opposite (upper bound by the maximum) is automatic. -/
def IsOrthogonalFamily (ν : VectorNorm F V) {ι : Type u} [Fintype ι] (b : ι → V) : Prop :=
  ∀ (c : ι → F) (i : ι), ν (c i • b i) ≤ ν (∑ j, c j • b j)

/-- A basis is adapted to a norm if it is orthogonal for that norm. -/
def IsAdaptedBasis (ν : VectorNorm F V) {ι : Type u} [Fintype ι] (b : Module.Basis ι F V) : Prop :=
  ν.IsOrthogonalFamily b

variable {ν : VectorNorm F V}

theorem IsOrthogonalFamily.linearIndependent {ι : Type u} [Fintype ι] {b : ι → V}
    (hb : ν.IsOrthogonalFamily b) (hb0 : ∀ i, b i ≠ 0) : LinearIndependent F b := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := hb c i
  rw [hc, map_zero, ν.map_smul] at h
  by_contra hi
  exact (mul_pos (norm_pos_iff.2 hi) (ν.pos (hb0 i))).not_ge h

/-- Bounding an adapted norm is equivalent to bounding each weighted coordinate. -/
theorem IsAdaptedBasis.apply_le_iff {ι : Type u} [Fintype ι] {b : Module.Basis ι F V}
    (hb : ν.IsAdaptedBasis b) {C : ℝ} (hC : 0 ≤ C) (a : V) :
    ν a ≤ C ↔ ∀ i, ‖b.repr a i‖ * ν (b i) ≤ C := by
  constructor
  · intro ha i
    have h := hb (b.repr a) i
    rw [b.sum_repr, ν.map_smul] at h
    exact h.trans ha
  · intro h
    by_contra! ha
    have h' : ν (∑ i, b.repr a i • b i) < ν a :=
      ν.apply_sum_lt Finset.univ _ (hC.trans_lt ha) fun i _ => by
        rw [ν.map_smul]
        exact (h i).trans_lt ha
    rw [b.sum_repr] at h'
    exact (lt_irrefl _) h'

/-- In an adapted basis the norm is the supremum of the weighted coordinates. -/
theorem IsAdaptedBasis.apply_eq_iSup {ι : Type u} [Fintype ι] {b : Module.Basis ι F V}
    (hb : ν.IsAdaptedBasis b) (a : V) : ν a = ⨆ i, ‖b.repr a i‖ * ν (b i) := by
  let f := fun i : ι => ‖b.repr a i‖ * ν (b i)
  have hf0 : ∀ i, 0 ≤ f i := fun i => mul_nonneg (norm_nonneg _) (ν.nonneg _)
  exact le_antisymm ((hb.apply_le_iff (Real.iSup_nonneg hf0) a).2 fun i =>
    le_ciSup (Set.finite_range f).bddAbove i)
    (Real.iSup_le ((hb.apply_le_iff (ν.nonneg a) a).1 le_rfl) (ν.nonneg a))

section LocalField

variable {k : Type v} [NontriviallyNormedField k] [ProperSpace k]
  {E : Type w} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
  (ν : VectorNorm k E)

/-- Every subspace has a closest point of minimal norm-distance to a given vector. Use
properness for the given vector norm, without adding any global instances on `E`. -/
private theorem exists_closest_mem (W : Submodule k E) (x : E) :
    ∃ w ∈ W, ∀ w' ∈ W, ν (x - w) ≤ ν (x - w') := by
  let n : AddGroupNorm E :=
    { toFun := ν
      map_zero' := ν.map_zero
      add_le' := fun a b => (ν.add_le_max a b).trans (max_le_add_of_nonneg (ν.nonneg a) (ν.nonneg b))
      neg' := ν.apply_neg
      eq_zero_of_map_eq_zero' := fun a h => by
        by_contra ha
        exact (ν.pos ha).ne' h }
  let : NormedAddCommGroup E := n.toNormedAddCommGroup
  let : NormedSpace k E :=
    { toModule := ‹Module k E›
      norm_smul_le := fun a b => (ν.map_smul a b).le }
  let : ProperSpace E := FiniteDimensional.proper k E
  obtain ⟨w, hw, hmin⟩ := W.closed_of_finiteDimensional.exists_infDist_eq_dist
    ⟨0, W.zero_mem⟩ x
  refine ⟨w, hw, fun w' hw' => ?_⟩
  have h := Metric.infDist_le_dist_of_mem (x := x) hw'
  rw [hmin, dist_eq_norm, dist_eq_norm] at h
  exact h

/-- A proper subspace has an orthogonal line outside it for the given norm. -/
private theorem exists_orthogonal_line (W : Submodule k E) (x : E) (hx : x ∉ W) :
    ∃ y ∉ W, ∀ (t : k) (u : E), u ∈ W → ν (u + t • y) = max (ν u) (ν (t • y)) := by
  obtain ⟨w, hw, hmin⟩ := ν.exists_closest_mem W x
  let y := x - w
  have hy : y ∉ W := fun h => hx (by simpa only [y, sub_add_cancel] using W.add_mem h hw)
  have hbase (u : E) (hu : u ∈ W) : ν (u + y) = max (ν u) (ν y) := by
    have hle : ν y ≤ ν (u + y) := by
      have heq : u + y = x - (w - u) := by dsimp [y]; abel
      rw [heq]
      exact hmin _ (W.sub_mem hw hu)
    by_cases h : ν y < ν u
    · rw [ν.apply_add_eq_of_lt h, max_eq_left h.le]
    · exact le_antisymm (ν.add_le_max u y) (max_le ((not_lt.1 h).trans hle) hle)
  refine ⟨y, hy, fun t u hu => ?_⟩
  by_cases ht : t = 0
  · simp [ht, max_eq_left (ν.nonneg u)]
  have heq : t • (t⁻¹ • u + y) = u + t • y := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul]
  rw [← heq, ν.map_smul, hbase _ (W.smul_mem _ hu), mul_max_of_nonneg _ _ (norm_nonneg t),
    ← ν.map_smul, ← ν.map_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]

private theorem exists_orthogonal_family_with_first {a : E} (ha : a ≠ 0) {n : ℕ}
    (hn : n + 1 ≤ Module.finrank k E) :
    ∃ b : Fin (n + 1) → E, ν.IsOrthogonalFamily b ∧ (∀ i, b i ≠ 0) ∧ b 0 = a := by
  induction n with
  | zero =>
    refine ⟨fun _ => a, fun c i => ?_, fun _ => ha, rfl⟩
    have hi : i = 0 := Fin.ext (Nat.le_zero.mp (Nat.le_of_lt_succ i.isLt))
    rw [Fin.sum_univ_one, hi]
  | succ n ih =>
    obtain ⟨b, horth, hb, hfirst⟩ := ih (by omega)
    have hli := horth.linearIndependent hb
    let W := Submodule.span k (range b)
    have hW : W ≠ ⊤ := by
      intro htop
      have hr : Module.finrank k W = Fintype.card (Fin (n + 1)) := finrank_span_eq_card hli
      rw [htop, finrank_top, Fintype.card_fin] at hr
      omega
    obtain ⟨x, hx⟩ : ∃ x : E, x ∉ W := by
      by_contra! h
      exact hW (top_unique fun x _ => h x)
    obtain ⟨y, hy, hmax⟩ := ν.exists_orthogonal_line W x hx
    refine ⟨Fin.snoc b y, ?_, ?_, ?_⟩
    · intro c i
      have hsum : (∑ j : Fin (n + 1), c j.castSucc • b j) ∈ W :=
        W.sum_mem fun j _ => W.smul_mem _ (Submodule.subset_span (mem_range_self j))
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hmax _ _ hsum]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
        exact le_max_right _ _
      · rw [Fin.snoc_castSucc]
        exact (horth (fun j => c j.castSucc) j).trans (le_max_left _ _)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
        exact fun hy0 => hy (hy0 ▸ W.zero_mem)
      · rw [Fin.snoc_castSucc]
        exact hb j
    · simpa only [← Fin.castSucc_zero, Fin.snoc_castSucc] using hfirst

/-- An ultrametric vector norm over a proper field has an adapted basis beginning with any
prescribed nonzero vector. -/
theorem exists_isAdaptedBasis_with_first {n : ℕ} (hn : Module.finrank k E = n + 1)
    {a : E} (ha : a ≠ 0) :
    ∃ b : Module.Basis (Fin (n + 1)) k E, ν.IsAdaptedBasis b ∧ b 0 = a := by
  obtain ⟨b, horth, hb, hfirst⟩ := ν.exists_orthogonal_family_with_first ha hn.ge
  have hli := horth.linearIndependent hb
  have hsp : Submodule.span k (range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hn])
  let B := Module.Basis.mk hli hsp.ge
  have hB : (B : Fin (n + 1) → E) = b := funext (Module.Basis.mk_apply hli hsp.ge)
  refine ⟨B, ?_, ?_⟩
  · unfold IsAdaptedBasis
    rwa [hB]
  · rwa [hB]

/-- Adapted bases exist in every finite dimension (Rémy–Thuillier–Werner, Proposition 1.20). -/
theorem exists_isAdaptedBasis :
    ∃ b : Module.Basis (Fin (Module.finrank k E)) k E, ν.IsAdaptedBasis b := by
  rcases Nat.eq_zero_or_pos (Module.finrank k E) with h | h
  · refine ⟨Module.finBasis k E, fun c i => ?_⟩
    have hi := i.isLt
    omega
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    obtain ⟨b, hb, -⟩ := ν.exists_isAdaptedBasis_with_first hn
      ((Module.finBasis k E).ne_zero (⟨0, h⟩ : Fin (Module.finrank k E)))
    rw [hn]
    exact ⟨b, hb⟩

end LocalField

end Langlands.Analytic.VectorNorm
