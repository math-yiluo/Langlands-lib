import Langlands.Algebra.DivisionAlgebraNorm
import Langlands.Shimura.Levels
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Units

/-!
# The maximal compact subgroup and principal congruence subgroups of a local division algebra

Let `k` be a complete, locally compact, nonarchimedean nontrivially normed field and `D` a
finite-dimensional division `k`-algebra with its `k`-module topology. The elements of
normalized determinant norm at most one form the integer ring `O_D`; its unit group is a
compact open subgroup of `Dˣ` containing every compact subgroup. For `0 < r < 1` the elements
`g` with `|g - 1| ≤ r` form a compact open subgroup; for a uniformizer `ϖ` of `k` and `N ≥ 1`
this is `1 + ϖ^N O_D`.
-/

noncomputable section

set_option autoImplicit false

universe u v

namespace Langlands.Shimura.LocalDivision

open Langlands.CentralDivision Metric

variable (k : Type u) [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
variable (D : Type v) [DivisionRing D] [Algebra k D] [FiniteDimensional k D]

/-- The integer ring `O_D` of `D`: the elements of normalized determinant norm at most one. -/
def integerRing : Subring D where
  carrier := {x | regularAbsoluteValue k D x ≤ 1}
  mul_mem' {a b} ha hb := by
    change regularAbsoluteValue k D a ≤ 1 at ha
    change regularAbsoluteValue k D b ≤ 1 at hb
    change regularAbsoluteValue k D (a * b) ≤ 1
    rw [map_mul]
    calc regularAbsoluteValue k D a * regularAbsoluteValue k D b ≤ 1 * 1 :=
          mul_le_mul ha hb (by positivity) zero_le_one
      _ = 1 := one_mul 1
  one_mem' := by
    change regularAbsoluteValue k D 1 ≤ 1
    rw [map_one]
  add_mem' {a b} ha hb := (regularAbsoluteValue_add_le k D a b).trans (max_le ha hb)
  zero_mem' := by
    change regularAbsoluteValue k D 0 ≤ 1
    rw [map_zero]
    exact zero_le_one
  neg_mem' {a} ha := by
    change regularAbsoluteValue k D (-a) ≤ 1
    rw [AbsoluteValue.map_neg]
    exact ha

theorem mem_integerRing (x : D) :
    x ∈ integerRing k D ↔ regularAbsoluteValue k D x ≤ 1 := Iff.rfl

/-- An element `g` with `|g - 1| < 1` has `|g| = 1`. -/
theorem regularAbsoluteValue_eq_one_of_sub_one_lt (g : D)
    (hg : regularAbsoluteValue k D (g - 1) < 1) : regularAbsoluteValue k D g = 1 := by
  have h1 : regularAbsoluteValue k D g ≤ 1 := by
    have := regularAbsoluteValue_add_le k D (g - 1) 1
    rw [sub_add_cancel, map_one] at this
    exact this.trans (max_le hg.le le_rfl)
  have h2 : 1 ≤ regularAbsoluteValue k D g := by
    by_contra h
    rw [not_le] at h
    have := regularAbsoluteValue_add_le k D g (-(g - 1))
    have e : g + -(g - 1) = 1 := by abel
    rw [e, map_one, AbsoluteValue.map_neg] at this
    exact absurd (this.trans_lt (max_lt h hg)) (lt_irrefl 1)
  exact le_antisymm h1 h2

/-- The congruence subgroup `{g | |g - 1| ≤ r}` of `Dˣ`, for `0 ≤ r < 1`. -/
def congruenceSubgroup (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) : Subgroup Dˣ where
  carrier := {g | regularAbsoluteValue k D ((g : D) - 1) ≤ r}
  one_mem' := by
    change regularAbsoluteValue k D (((1 : Dˣ) : D) - 1) ≤ r
    rw [Units.val_one, sub_self, map_zero]
    exact hr0
  mul_mem' {g h} hg hh := by
    change regularAbsoluteValue k D ((g : D) - 1) ≤ r at hg
    change regularAbsoluteValue k D ((h : D) - 1) ≤ r at hh
    change regularAbsoluteValue k D (((g * h : Dˣ) : D) - 1) ≤ r
    rw [Units.val_mul]
    have hh1 : regularAbsoluteValue k D (h : D) = 1 :=
      regularAbsoluteValue_eq_one_of_sub_one_lt k D h (hh.trans_lt hr)
    have : (g : D) * h - 1 = ((g : D) - 1) * h + ((h : D) - 1) := by noncomm_ring
    rw [this]
    refine (regularAbsoluteValue_add_le k D _ _).trans (max_le ?_ hh)
    rw [map_mul, hh1, mul_one]
    exact hg
  inv_mem' {g} hg := by
    change regularAbsoluteValue k D ((g : D) - 1) ≤ r at hg
    change regularAbsoluteValue k D (((g⁻¹ : Dˣ) : D) - 1) ≤ r
    have hg1 : regularAbsoluteValue k D (g : D) = 1 :=
      regularAbsoluteValue_eq_one_of_sub_one_lt k D g (hg.trans_lt hr)
    have hinv : regularAbsoluteValue k D ((g⁻¹ : Dˣ) : D) = 1 := by
      have := map_mul (regularAbsoluteValue k D) ((g⁻¹ : Dˣ) : D) (g : D)
      rw [Units.inv_mul, map_one, hg1, mul_one] at this
      exact this.symm
    have : ((g⁻¹ : Dˣ) : D) - 1 = -(((g⁻¹ : Dˣ) : D) * ((g : D) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [this, AbsoluteValue.map_neg, map_mul, hinv, one_mul]
    exact hg

theorem mem_congruenceSubgroup (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) (g : Dˣ) :
    g ∈ congruenceSubgroup k D r hr0 hr ↔ regularAbsoluteValue k D ((g : D) - 1) ≤ r :=
  Iff.rfl

theorem congruenceSubgroup_le_units (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    congruenceSubgroup k D r hr0 hr ≤ (integerRing k D).toSubmonoid.units := by
  intro g hg
  have hg1 := regularAbsoluteValue_eq_one_of_sub_one_lt k D g (hg.trans_lt hr)
  have hinv : regularAbsoluteValue k D ((g⁻¹ : Dˣ) : D) = 1 := by
    have := map_mul (regularAbsoluteValue k D) ((g⁻¹ : Dˣ) : D) (g : D)
    rw [Units.inv_mul, map_one, hg1, mul_one] at this
    exact this.symm
  exact ⟨hg1.le, hinv.le⟩

/-- For a nonzero `ϖ` in `k` with `|ϖ| < 1` and `N`, the congruence subgroup of radius
`|ϖ|^N` is `1 + ϖ^N O_D`. -/
theorem mem_congruenceSubgroup_iff_exists (ϖ : k) (hϖ : ϖ ≠ 0) (N : ℕ) (hN : ‖ϖ‖ ^ N < 1)
    (g : Dˣ) :
    g ∈ congruenceSubgroup k D (‖ϖ‖ ^ N) (by positivity) hN ↔
      ∃ y ∈ integerRing k D, (g : D) = 1 + ϖ ^ N • y := by
  rw [mem_congruenceSubgroup]
  constructor
  · intro hg
    refine ⟨(ϖ ^ N)⁻¹ • ((g : D) - 1), ?_, ?_⟩
    · rw [mem_integerRing, Algebra.smul_def, map_mul, regularAbsoluteValue_algebraMap,
        norm_inv, norm_pow]
      have hpos : 0 < ‖ϖ‖ ^ N := by positivity
      rw [inv_mul_le_iff₀ hpos, mul_one]
      exact hg
    · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero N hϖ), one_smul, add_sub_cancel]
  · rintro ⟨y, hy, hgy⟩
    rw [hgy, add_sub_cancel_left, Algebra.smul_def, map_mul, regularAbsoluteValue_algebraMap,
      norm_pow]
    calc ‖ϖ‖ ^ N * regularAbsoluteValue k D y ≤ ‖ϖ‖ ^ N * 1 :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ = ‖ϖ‖ ^ N := mul_one _

section Normed

/-- The regular norm is nonarchimedean. -/
theorem isUltrametricDist_regular :
    letI := regularNormedRing k D
    IsUltrametricDist D :=
  letI := regularNormedRing k D
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (regularAbsoluteValue_add_le k D)

/-- With the normed structure of the regular norm, `D` carries the `k`-module topology. -/
theorem isModuleTopology_regular :
    letI := regularNormedRing k D
    IsModuleTopology k D :=
  letI := regularNormedRing k D
  letI := regularNormedAlgebra k D
  isModuleTopologyOfFiniteDimensional

theorem isOpen_integerRing_regular :
    letI := regularNormedRing k D
    IsOpen (integerRing k D : Set D) := by
  let := regularNormedRing k D
  have := isUltrametricDist_regular k D
  have h : (integerRing k D : Set D) = closedBall 0 1 := by
    ext x
    rw [mem_closedBall, dist_zero_right]
    rfl
  rw [h]
  exact IsUltrametricDist.isOpen_closedBall 0 one_ne_zero

theorem isCompact_integerRing_regular [LocallyCompactSpace k] :
    letI := regularNormedRing k D
    IsCompact (integerRing k D : Set D) := by
  let := regularNormedRing k D
  let := regularNormedAlgebra k D
  have := FiniteDimensional.proper k D
  have h : (integerRing k D : Set D) = closedBall 0 1 := by
    ext x
    rw [mem_closedBall, dist_zero_right]
    rfl
  rw [h]
  exact isCompact_closedBall 0 1

end Normed

/-- The topology of the regular norm. -/
abbrev regularTopology : TopologicalSpace D :=
  @UniformSpace.toTopologicalSpace D (@PseudoMetricSpace.toUniformSpace D
    (@SeminormedRing.toPseudoMetricSpace D (@NormedRing.toSeminormedRing D (regularNormedRing k D))))

section Topology

variable [TopologicalSpace D] [IsModuleTopology k D]

/-- The `k`-module topology of `D` is the topology of the regular norm. -/
theorem topology_eq_regular : ‹TopologicalSpace D› = regularTopology k D :=
  (eq_moduleTopology k D).trans
    (@eq_moduleTopology k _ D _ _ (regularTopology k D) (isModuleTopology_regular k D)).symm

theorem isOpen_integerRing : IsOpen (integerRing k D : Set D) := by
  rw [topology_eq_regular k D]
  exact isOpen_integerRing_regular k D

theorem isCompact_integerRing [LocallyCompactSpace k] :
    IsCompact (integerRing k D : Set D) := by
  rw [topology_eq_regular k D]
  exact isCompact_integerRing_regular k D

include k in
theorem t2Space_of_isModuleTopology : T2Space D := by
  rw [topology_eq_regular k D]
  let := regularNormedRing k D
  infer_instance

theorem continuous_regularAbsoluteValue : Continuous (regularAbsoluteValue k D) := by
  rw [topology_eq_regular k D]
  let := regularNormedRing k D
  exact continuous_norm

theorem isClosed_congruenceBall (r : ℝ) :
    IsClosed {x : D | regularAbsoluteValue k D (x - 1) ≤ r} :=
  have := IsModuleTopology.isTopologicalAddGroup k D
  isClosed_le ((continuous_regularAbsoluteValue k D).comp (continuous_id.sub continuous_const))
    continuous_const

theorem isOpen_congruenceBall (r : ℝ) (hr : 0 < r) :
    IsOpen {x : D | regularAbsoluteValue k D (x - 1) ≤ r} := by
  rw [topology_eq_regular k D]
  let := regularNormedRing k D
  have := isUltrametricDist_regular k D
  have h : {x : D | regularAbsoluteValue k D (x - 1) ≤ r} = closedBall 1 r := by
    ext x
    rw [mem_closedBall, dist_eq_norm]
    rfl
  rw [h]
  exact IsUltrametricDist.isOpen_closedBall 1 hr.ne'

variable [LocallyCompactSpace k]

/-- The unit group `O_Dˣ` of the integer ring, a compact open level of `Dˣ`. -/
def maximalCompactLevel : CompactOpenLevel Dˣ where
  openSubgroup :=
    { toSubgroup := (integerRing k D).toSubmonoid.units
      isOpen' := by
        have hO := isOpen_integerRing k D
        exact (hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv) }
  isCompact := by
    have := t2Space_of_isModuleTopology k D
    have : IsTopologicalRing D := IsModuleTopology.isTopologicalRing k D
    exact Submonoid.units_isCompact (isCompact_integerRing k D)

theorem mem_maximalCompactLevel (g : Dˣ) :
    g ∈ (maximalCompactLevel k D).subgroup ↔
      regularAbsoluteValue k D (g : D) ≤ 1 ∧ regularAbsoluteValue k D ((g⁻¹ : Dˣ) : D) ≤ 1 :=
  Iff.rfl

/-- Every compact subgroup of `Dˣ` is contained in `O_Dˣ`: the maximal compact level is the
unique maximal compact subgroup. -/
theorem le_maximalCompactLevel_of_isCompact (H : Subgroup Dˣ) (hH : IsCompact (H : Set Dˣ)) :
    H ≤ (maximalCompactLevel k D).subgroup := by
  have hf : Continuous fun g : Dˣ => regularAbsoluteValue k D (g : D) :=
    (continuous_regularAbsoluteValue k D).comp Units.continuous_val
  obtain ⟨M, hM⟩ := (hH.image hf).isBounded.bddAbove
  have key : ∀ h ∈ H, regularAbsoluteValue k D (h : D) ≤ 1 := by
    intro h hh
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
    have hmem : regularAbsoluteValue k D ((h ^ n : Dˣ) : D) ∈
        (fun g : Dˣ => regularAbsoluteValue k D (g : D)) '' (H : Set Dˣ) :=
      ⟨h ^ n, H.pow_mem hh n, rfl⟩
    have := hM hmem
    rw [Units.val_pow_eq_pow_val, map_pow] at this
    exact absurd this (not_le.mpr hn)
  intro h hh
  exact ⟨key h hh, key h⁻¹ (H.inv_mem hh)⟩

/-- The congruence level `{g | |g - 1| ≤ r}` of `Dˣ`, for `0 < r < 1`. -/
def congruenceLevel (r : ℝ) (hr0 : 0 < r) (hr : r < 1) : CompactOpenLevel Dˣ where
  openSubgroup :=
    { toSubgroup := congruenceSubgroup k D r hr0.le hr
      isOpen' := (isOpen_congruenceBall k D r hr0).preimage Units.continuous_val }
  isCompact := by
    refine (maximalCompactLevel k D).isCompact.of_isClosed_subset
      ((isClosed_congruenceBall k D r).preimage Units.continuous_val) ?_
    exact congruenceSubgroup_le_units k D r hr0.le hr

theorem congruenceLevel_le_maximalCompactLevel (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    (congruenceLevel k D r hr0 hr).subgroup ≤ (maximalCompactLevel k D).subgroup :=
  congruenceSubgroup_le_units k D r hr0.le hr

end Topology

end Langlands.Shimura.LocalDivision
