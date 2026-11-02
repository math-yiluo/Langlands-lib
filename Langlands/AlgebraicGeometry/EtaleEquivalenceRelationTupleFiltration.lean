import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleBound
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPointTopology

/-! # A finite invariant filtration from distinct related tuples -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u})

/-- The open saturation of an open subset under the actual point relation. -/
def pointSaturationOpen (W : E.U.Opens) : E.U.Opens := by
  let := E.etale_t
  exact ⟨E.t '' (E.s ⁻¹' (W : Set E.U)),
    E.t.isOpenMap _ (W.isOpen.preimage E.s.continuous)⟩

theorem mem_pointSaturationOpen (W : E.U.Opens) (x : E.U) :
    x ∈ E.pointSaturationOpen W ↔
      ∃ y ∈ W, E.PointRel y x := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨E.s r, hr, r, rfl, rfl⟩
  · rintro ⟨y, hy, r, hrs, hrt⟩
    exact ⟨r, by simpa [hrs] using hy, hrt⟩

theorem le_pointSaturationOpen (W : E.U.Opens) : W ≤ E.pointSaturationOpen W := by
  intro x hx
  exact (E.mem_pointSaturationOpen W x).mpr ⟨x, hx, E.pointRel_refl x⟩

theorem pointSaturationOpen_mono : Monotone E.pointSaturationOpen := by
  intro W V h x hx
  obtain ⟨y, hy, hxy⟩ := (E.mem_pointSaturationOpen W x).mp hx
  exact (E.mem_pointSaturationOpen V x).mpr ⟨y, h hy, hxy⟩

theorem pointSaturationOpen_invariant (W : E.U.Opens) :
    E.PointInvariant (E.pointSaturationOpen W : Set E.U) := by
  intro x y hxy hx
  obtain ⟨z, hz, hzx⟩ := (E.mem_pointSaturationOpen W x).mp hx
  exact (E.mem_pointSaturationOpen W y).mpr ⟨z, hz, E.pointRel_trans hzx hxy⟩

theorem pointSaturationOpen_eq_self (W : E.U.Opens)
    (hW : E.PointInvariant (W : Set E.U)) : E.pointSaturationOpen W = W := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := (E.mem_pointSaturationOpen W x).mp hx
    exact hW hyx hy
  · exact E.le_pointSaturationOpen W

@[simp] theorem pointSaturationOpen_idem (W : E.U.Opens) :
    E.pointSaturationOpen (E.pointSaturationOpen W) = E.pointSaturationOpen W :=
  E.pointSaturationOpen_eq_self _ (E.pointSaturationOpen_invariant W)

@[simp] theorem pointSaturationOpen_top : E.pointSaturationOpen ⊤ = ⊤ := by
  apply top_unique
  exact E.le_pointSaturationOpen ⊤

@[simp] theorem pointSaturationOpen_bot : E.pointSaturationOpen ⊥ = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, _⟩ := (E.mem_pointSaturationOpen ⊥ x).mp hx
    exact hy.elim
  · exact bot_le

theorem pointSaturationOpen_isCompact [QuasiCompact E.s]
    (W : E.U.Opens) (hW : IsCompact (W : Set E.U)) :
    IsCompact (E.pointSaturationOpen W : Set E.U) :=
  (E.s.isCompact_preimage hW).image E.t.continuous

variable [IsSeparated E.s]

/-- The open image of the zeroth coordinate of distinct related tuples. -/
def tupleImageOpen (n : ℕ) : E.U.Opens :=
  ⟨Set.range (E.tupleDistinctProjection n 0),
    (E.tupleDistinctProjection n 0).isOpenMap.isOpen_range⟩

/-- The invariant open saturation of the length `n + 1` distinct-tuple image. -/
def tupleThresholdOpen (n : ℕ) : E.U.Opens :=
  E.pointSaturationOpen (E.tupleImageOpen n)

theorem tupleThresholdOpen_invariant (n : ℕ) :
    E.PointInvariant (E.tupleThresholdOpen n : Set E.U) :=
  E.pointSaturationOpen_invariant _

theorem tupleThresholdOpen_preimage_eq (n : ℕ) :
    E.s ⁻¹ᵁ E.tupleThresholdOpen n = E.t ⁻¹ᵁ E.tupleThresholdOpen n :=
  Opens.ext (E.pointInvariant_preimage_eq (E.tupleThresholdOpen_invariant n))

theorem tupleImageOpen_antitone : Antitone E.tupleImageOpen := by
  intro m n hmn x hx
  obtain ⟨y, rfl⟩ := hx
  let a := Fin.castLE (Nat.succ_le_succ hmn)
  refine ⟨E.tupleDistinctReindex a (Fin.castLE_injective _) y, ?_⟩
  change (E.tupleDistinctReindex a (Fin.castLE_injective _) ≫
    E.tupleDistinctProjection m 0) y = E.tupleDistinctProjection n 0 y
  rw [E.tupleDistinctReindex_projection]
  rfl

theorem tupleThresholdOpen_antitone : Antitone E.tupleThresholdOpen :=
  fun _ _ h => E.pointSaturationOpen_mono (E.tupleImageOpen_antitone h)

@[simp] theorem tupleImageOpen_zero : E.tupleImageOpen 0 = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨⟨x, ?_⟩, ?_⟩
  · rw [E.mem_tupleDistinctOpen]
    intro i j hij
    exact (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim
  · rfl

@[simp] theorem tupleThresholdOpen_zero : E.tupleThresholdOpen 0 = ⊤ := by
  simp [tupleThresholdOpen]

/-- The set difference between consecutive threshold opens. This is a locus
of underlying scheme points, without a chosen scheme structure. -/
def tupleDegreeLocus (n : ℕ) : Set E.U :=
  (E.tupleThresholdOpen n : Set E.U) \ E.tupleThresholdOpen (n + 1)

theorem tupleDegreeLocus_isLocallyClosed (n : ℕ) :
    IsLocallyClosed (E.tupleDegreeLocus n) :=
  ⟨E.tupleThresholdOpen n, (E.tupleThresholdOpen (n + 1) : Set E.U)ᶜ,
    (E.tupleThresholdOpen n).isOpen, (E.tupleThresholdOpen (n + 1)).isOpen.isClosed_compl,
    rfl⟩

theorem tupleDegreeLocus_invariant (n : ℕ) :
    E.PointInvariant (E.tupleDegreeLocus n) := by
  intro x y hxy hx
  exact ⟨E.tupleThresholdOpen_invariant n hxy hx.1,
    fun hy => hx.2 (E.tupleThresholdOpen_invariant (n + 1) (E.pointRel_symm hxy) hy)⟩

theorem tupleDegreeLocus_disjoint {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (E.tupleDegreeLocus m) (E.tupleDegreeLocus n) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hx.2 (E.tupleThresholdOpen_antitone (Nat.succ_le_of_lt h) hy.1)
  · exact hy.2 (E.tupleThresholdOpen_antitone (Nat.succ_le_of_lt h) hx.1)

section Affine

variable [IsAffine E.U] [IsAffine E.R]

theorem tupleImageOpen_isCompact (n : ℕ) :
    IsCompact (E.tupleImageOpen n : Set E.U) :=
  isCompact_range (E.tupleDistinctProjection n 0).continuous

theorem tupleThresholdOpen_isCompact (n : ℕ) :
    IsCompact (E.tupleThresholdOpen n : Set E.U) :=
  E.pointSaturationOpen_isCompact _ (E.tupleImageOpen_isCompact n)

theorem tupleImageOpen_eq_bot (n : ℕ) (hn : E.tupleLengthBound ≤ n) :
    E.tupleImageOpen n = ⊥ := by
  let := E.tupleDistinctScheme_isEmpty n hn
  apply Opens.ext
  exact Set.range_eq_empty _

theorem tupleThresholdOpen_eq_bot (n : ℕ) (hn : E.tupleLengthBound ≤ n) :
    E.tupleThresholdOpen n = ⊥ := by
  simp [tupleThresholdOpen, E.tupleImageOpen_eq_bot n hn]

/-- Every underlying point lies in a unique difference of consecutive opens,
with an index strictly below the uniform tuple-length bound. -/
theorem exists_unique_tupleDegreeLocus (x : E.U) :
    ∃! n : ℕ, n < E.tupleLengthBound ∧ x ∈ E.tupleDegreeLocus n := by
  classical
  have hb : x ∉ E.tupleThresholdOpen E.tupleLengthBound := by
    rw [E.tupleThresholdOpen_eq_bot _ le_rfl]
    simp
  have hex : ∃ k, x ∉ E.tupleThresholdOpen k := ⟨_, hb⟩
  have hz : Nat.find hex ≠ 0 := by
    intro h
    have hnot := Nat.find_spec hex
    rw [h, E.tupleThresholdOpen_zero] at hnot
    exact hnot (Set.mem_univ x)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
  have hle : n + 1 ≤ E.tupleLengthBound := by
    simpa only [hn] using Nat.find_min' hex hb
  have hmem : x ∈ E.tupleDegreeLocus n := by
    constructor
    · by_contra hnot
      exact Nat.find_min hex (by omega) hnot
    · simpa [hn] using Nat.find_spec hex
  refine ⟨n, ⟨by omega, hmem⟩, ?_⟩
  intro m hm
  by_contra hmn
  exact Set.disjoint_left.mp (E.tupleDegreeLocus_disjoint hmn) hm.2 hmem

end Affine

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
