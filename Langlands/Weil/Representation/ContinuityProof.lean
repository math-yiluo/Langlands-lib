import Langlands.Weil.Representation.Continuity
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

open Topology Filter

namespace Langlands.Weil

/-- Repeated squaring excludes nontrivial small submonoids in a real normed algebra. -/
theorem eq_one_of_small_submonoid {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (S : Submonoid A) (hS : ∀ a ∈ S, ‖a - 1‖ ≤ (1 / 2 : ℝ)) :
    ∀ a ∈ S, a = 1 := by
  have growth (a : A) (ha : a ∈ S) :
      (3 / 2 : ℝ) * ‖a - 1‖ ≤ ‖a * a - 1‖ := by
    have hid : (2 : ℝ) • (a - 1) = (a * a - 1) - (a - 1) * (a - 1) := by
      rw [two_smul]
      noncomm_ring
    have h := norm_sub_le (a * a - 1) ((a - 1) * (a - 1))
    rw [← hid, norm_smul] at h
    norm_num at h
    have hm := norm_mul_le (a - 1) (a - 1)
    have hb := hS a ha
    nlinarith [norm_nonneg (a - 1)]
  have bounds (n : ℕ) : ∀ a ∈ S, ‖a - 1‖ ≤ (2 / 3 : ℝ) ^ n := by
    induction n with
    | zero =>
      intro a ha
      have := hS a ha
      norm_num
      linarith
    | succ n ih =>
      intro a ha
      have h := ih (a * a) (S.mul_mem ha ha)
      have hg := growth a ha
      rw [pow_succ]
      nlinarith
  intro a ha
  have hz : ‖a - 1‖ ≤ 0 :=
    ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 / 3 : ℝ))
        (by norm_num) (by norm_num))
      (Eventually.of_forall fun n => bounds n a ha)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- A homomorphism with open kernel is continuous into any topology on its target. -/
theorem continuous_of_open_kernel {G M : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Monoid M] [TopologicalSpace M]
    (f : G →* M) (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  let : DiscreteTopology (G ⧸ f.ker) := QuotientGroup.discreteTopology hf
  exact (continuous_of_discreteTopology (f := QuotientGroup.lift f.ker f le_rfl)).comp
    QuotientGroup.continuous_mk

/-- The range of a homomorphism from a compact group with open kernel is finite. -/
theorem finite_range_of_open_kernel {G M : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [Monoid M]
    (f : G →* M) (hf : IsOpen (f.ker : Set G)) : (Set.range f).Finite := by
  let := f.ker.quotient_finite_of_isOpen hf
  exact (Set.finite_range (QuotientGroup.lift f.ker f le_rfl)).subset
    (by rintro _ ⟨g, rfl⟩; exact ⟨QuotientGroup.mk g, rfl⟩)

/-- Finite range and closed kernel imply open kernel, without compactness. -/
theorem open_kernel_of_finite_range_of_closed {G M : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Monoid M]
    (f : G →* M) (hf : (Set.range f).Finite) (hc : IsClosed (f.ker : Set G)) :
    IsOpen (f.ker : Set G) := by
  let l := QuotientGroup.lift f.ker f le_rfl
  have hr (q : G ⧸ f.ker) : l q ∈ Set.range f := by
    induction q using QuotientGroup.induction_on with
    | H g => exact ⟨g, rfl⟩
  let := hf.to_subtype
  let : Finite (G ⧸ f.ker) := Finite.of_injective
    (fun q => (⟨l q, hr q⟩ : Set.range f)) (by
      intro a b h
      exact (QuotientGroup.injective_lift_iff f.ker f le_rfl).mpr rfl (congrArg Subtype.val h))
  let : f.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact f.ker.isOpen_of_isClosed_of_finiteIndex hc

universe uW uV

/-- Continuous complex representations of nonarchimedean groups have open kernel. -/
theorem open_kernel_of_continuous_nonarchimedean_representation
    {K : Type uW} [Group K] [TopologicalSpace K] [NonarchimedeanGroup K]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ K V)
    (hc : Continuous (fun k => (ρ k).toContinuousLinearMap)) :
    IsOpen (ρ.ker : Set K) := by
  let f : K →* (V →L[ℂ] V) :=
    { toFun := fun k => (ρ k).toContinuousLinearMap
      map_one' := by ext v; simp
      map_mul' := by intro a b; ext v; simp }
  have hf : Continuous f := hc
  have hU : {k : K | ‖f k - 1‖ < (1 / 2 : ℝ)} ∈ 𝓝 (1 : K) := by
    apply (isOpen_lt (hf.sub continuous_const).norm continuous_const).mem_nhds
    simp
  obtain ⟨U, hU⟩ := NonarchimedeanGroup.is_nonarchimedean _ hU
  apply ρ.ker.isOpen_of_openSubgroup (U := U)
  intro k hk
  have he : f k = 1 := eq_one_of_small_submonoid (U.toSubmonoid.map f)
    (by rintro _ ⟨a, ha, rfl⟩; exact (hU ha).le) _ ⟨k, hk, rfl⟩
  change ρ k = 1
  ext v
  exact congrArg (fun T : V →L[ℂ] V => T v) he

/-- Restriction to an open subgroup detects openness of a homomorphism kernel. -/
theorem open_kernel_iff_open_restriction_kernel {G M : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Monoid M]
    (I : OpenSubgroup G) (f : G →* M) :
    IsOpen (f.ker : Set G) ↔ IsOpen ((f.comp I.toSubgroup.subtype).ker : Set I) := by
  constructor
  · intro h
    exact h.preimage continuous_subtype_val
  · intro h
    apply f.ker.isOpen_of_mem_nhds (g := 1)
    have ho := I.isOpen.isOpenMap_subtype_val _ h
    have hm : (1 : G) ∈ Subtype.val '' ((f.comp I.toSubgroup.subtype).ker : Set I) :=
      ⟨1, (f.comp I.toSubgroup.subtype).ker.one_mem, rfl⟩
    exact Filter.mem_of_superset (ho.mem_nhds hm) (by
      rintro _ ⟨i, hi, rfl⟩
      exact hi)

/-- An open representation kernel gives operator-norm continuity. -/
theorem representation_continuous_of_open_kernel
    {G : Type uW} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (ho : IsOpen (ρ.ker : Set G)) :
    Continuous (fun g => (ρ g).toContinuousLinearMap) := by
  let : DiscreteTopology (G ⧸ ρ.ker) := QuotientGroup.discreteTopology ho
  exact (continuous_of_discreteTopology
    (f := fun q => (QuotientGroup.lift ρ.ker ρ le_rfl q).toContinuousLinearMap)).comp
    QuotientGroup.continuous_mk

/-- The finite-inertia/open-kernel criterion includes the necessary closedness condition. -/
theorem open_inertia_kernel_iff_finite_range_and_closed
    {G : Type uW} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : OpenSubgroup G) [CompactSpace I]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ρ : Representation ℂ G V) :
    IsOpen ((ρ.comp I.toSubgroup.subtype).ker : Set I) ↔
      (Set.range (fun i : I => ρ (i : G))).Finite ∧
        IsClosed ((ρ.comp I.toSubgroup.subtype).ker : Set I) := by
  let : IsTopologicalGroup I := inferInstanceAs (IsTopologicalGroup I.toSubgroup)
  constructor
  · intro h
    exact ⟨finite_range_of_open_kernel _ h, Subgroup.isClosed_of_isOpen _ h⟩
  · rintro ⟨hf, hc⟩
    exact open_kernel_of_finite_range_of_closed _ hf hc

/-- Continuous representations of compact nonarchimedean groups have finite range.
No separation axiom is imposed on the group. -/
theorem continuous_compact_nonarchimedean_representation_finite_range
    (K : Type uW) [Group K] [TopologicalSpace K] [NonarchimedeanGroup K] [CompactSpace K]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ K V)
    (hc : Continuous (fun k => (ρ k).toContinuousLinearMap)) : (Set.range ρ).Finite :=
  finite_range_of_open_kernel ρ (open_kernel_of_continuous_nonarchimedean_representation ρ hc)

/-- All five continuity, kernel, and finite-inertia equivalences. -/
theorem representationContinuity : RepresentationContinuity.{uW, uV} := by
  intro W _ _ _ I _ _ V _ _ _ ρ
  dsimp only
  have horbit : Continuous (fun w => (ρ w).toContinuousLinearMap) ↔
      ∀ v : V, Continuous (fun w => ρ w v) := continuous_clm_apply
  have hjoint : Continuous (fun w => (ρ w).toContinuousLinearMap) ↔
      Continuous (fun x : W × V => ρ x.1 x.2) := by
    constructor
    · intro h
      exact (h.comp continuous_fst).clm_apply continuous_snd
    · intro h
      apply horbit.mpr
      intro v
      exact h.comp (continuous_id.prodMk continuous_const)
  have hinertia : Continuous (fun w => (ρ w).toContinuousLinearMap) ↔
      IsOpen ((ρ.comp I.toSubgroup.subtype).ker : Set I) := by
    constructor
    · intro h
      exact open_kernel_of_continuous_nonarchimedean_representation
        (ρ.comp I.toSubgroup.subtype) (h.comp continuous_subtype_val)
    · intro h
      exact representation_continuous_of_open_kernel ρ
        ((open_kernel_iff_open_restriction_kernel I ρ).mpr h)
  exact ⟨horbit, hjoint, hinertia,
    hinertia.trans (open_kernel_iff_open_restriction_kernel I ρ).symm,
    open_inertia_kernel_iff_finite_range_and_closed I ρ⟩

end Langlands.Weil
