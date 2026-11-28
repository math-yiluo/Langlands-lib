import Langlands.HarmonicAnalysis.Bicharacter.SelfDual
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# The lattices `ϖ ^ k R` of a compact open order

For a nonarchimedean local field `F`, an `F`-algebra `A` with its module topology, a compact
open subring `R` stable under the integers of `F` (`IsCompactOpenOrder`) and `ϖ ∈ F` with
`0 < |ϖ| < 1`, the additive subgroups `orderLevel R ϖ k = ϖ ^ k R` (`k ∈ ℤ`) are compact open,
decrease in `k`, multiply as `ϖ ^ a R · ϖ ^ b R ⊆ ϖ ^ (a + b) R`, exhaust `A`, form a basis of
neighbourhoods of `0` and, for finite-dimensional `A`, intersect in `0`; the elements of
`1 + ϖ R` are units with inverse in `R`.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open ValuativeRel Filter Topology

section Algebraic

variable {F : Type*} [Field F] [ValuativeRel F] {A : Type*} [Ring A] [Algebra F A]

/-- The preimage of `R` under `x ↦ ϖ ^ (-k) • x`. It equals `ϖ ^ k R` when `ϖ ≠ 0`. -/
def orderLevel (R : Subring A) (ϖ : F) (k : ℤ) : AddSubgroup A where
  carrier := {x | ϖ ^ (-k) • x ∈ R}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, smul_add] at ha hb ⊢
    exact R.add_mem ha hb
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq, smul_neg] at ha ⊢
    exact R.neg_mem ha

variable {R : Subring A} {ϖ : F}

omit [ValuativeRel F] in
theorem mem_orderLevel {k : ℤ} {x : A} : x ∈ orderLevel R ϖ k ↔ ϖ ^ (-k) • x ∈ R := Iff.rfl

omit [ValuativeRel F] in
@[simp]
theorem mem_orderLevel_zero {x : A} : x ∈ orderLevel R ϖ 0 ↔ x ∈ R := by
  simp [mem_orderLevel]

theorem smul_mem_orderLevel (hsmul : ∀ c : F, valuation F c ≤ 1 → ∀ x ∈ R, c • x ∈ R)
    {c : F} (hc : valuation F c ≤ 1) {k : ℤ} {x : A}
    (hx : x ∈ orderLevel R ϖ k) : c • x ∈ orderLevel R ϖ k := by
  rw [mem_orderLevel, smul_comm]
  exact hsmul c hc _ hx

variable (hϖ : ϖ ≠ 0)
include hϖ

theorem orderLevel_anti (hsmul : ∀ c : F, valuation F c ≤ 1 → ∀ x ∈ R, c • x ∈ R)
    (hϖ1 : valuation F ϖ < 1) {k l : ℤ} (hkl : k ≤ l) :
    orderLevel R ϖ l ≤ orderLevel R ϖ k := by
  intro x hx
  obtain ⟨n, rfl⟩ := Int.exists_add_of_le hkl
  rw [mem_orderLevel] at hx ⊢
  have : ϖ ^ (-k) • x = ϖ ^ n • ϖ ^ (-(k + n)) • x := by
    rw [smul_smul, ← zpow_natCast, ← zpow_add₀ hϖ]
    congr 2
    ring
  rw [this]
  refine hsmul _ ?_ _ hx
  rw [map_pow]
  exact pow_le_one₀ zero_le hϖ1.le

omit [ValuativeRel F] in
theorem zpow_smul_mem_orderLevel_iff (j k : ℤ) (x : A) :
    ϖ ^ j • x ∈ orderLevel R ϖ (k + j) ↔ x ∈ orderLevel R ϖ k := by
  rw [mem_orderLevel, mem_orderLevel, smul_smul, ← zpow_add₀ hϖ]
  congr! 3
  ring

omit [ValuativeRel F] in
theorem mul_mem_orderLevel {a b : ℤ} {x y : A} (hx : x ∈ orderLevel R ϖ a)
    (hy : y ∈ orderLevel R ϖ b) : x * y ∈ orderLevel R ϖ (a + b) := by
  rw [mem_orderLevel] at hx hy ⊢
  have : ϖ ^ (-(a + b)) • (x * y) = (ϖ ^ (-a) • x) * (ϖ ^ (-b) • y) := by
    rw [smul_mul_smul_comm, ← zpow_add₀ hϖ]
    congr 2; ring
  rw [this]
  exact R.mul_mem hx hy

omit [ValuativeRel F] in
theorem mul_mem_orderLevel_left {k : ℤ} {r x : A} (hr : r ∈ R) (hx : x ∈ orderLevel R ϖ k) :
    r * x ∈ orderLevel R ϖ k := by
  simpa using mul_mem_orderLevel hϖ (a := 0) (mem_orderLevel_zero.mpr hr) hx

omit [ValuativeRel F] in
theorem mul_mem_orderLevel_right {k : ℤ} {r x : A} (hr : r ∈ R) (hx : x ∈ orderLevel R ϖ k) :
    x * r ∈ orderLevel R ϖ k := by
  simpa using mul_mem_orderLevel hϖ (b := 0) hx (mem_orderLevel_zero.mpr hr)

end Algebraic

section Topological

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Powers of an element of valuation less than one tend to zero. -/
theorem tendsto_pow_atTop_nhds_zero_of_valuation_lt_one {ϖ : F} (h : valuation F ϖ < 1) :
    Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero F).tendsto_right_iff]
  intro γ _
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h γ
  filter_upwards [eventually_ge_atTop n] with k hk
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hk) hn

variable (F) {A : Type*} [Ring A] [Algebra F A] [TopologicalSpace A] [IsModuleTopology F A]

/-- A compact open subring of `A` stable under multiplication by the integers of `F`. -/
structure IsCompactOpenOrder (R : Subring A) : Prop where
  isCompact : IsCompact (R : Set A)
  isOpen : IsOpen (R : Set A)
  smul_mem : ∀ c : F, valuation F c ≤ 1 → ∀ x ∈ R, c • x ∈ R

variable {F} {R : Subring A} {ϖ : F}

variable (hR : IsCompactOpenOrder F R) (hϖ : ϖ ≠ 0) (hϖ1 : valuation F ϖ < 1)
include hR

omit [IsNonarchimedeanLocalField F] in
theorem isOpen_orderLevel (k : ℤ) : IsOpen (orderLevel R ϖ k : Set A) := by
  have := IsModuleTopology.toContinuousSMul F A
  exact hR.isOpen.preimage (continuous_const_smul (ϖ ^ (-k)))

omit [IsNonarchimedeanLocalField F] in
include hϖ in
theorem isCompact_orderLevel (k : ℤ) : IsCompact (orderLevel R ϖ k : Set A) := by
  have := IsModuleTopology.toContinuousSMul F A
  have : (orderLevel R ϖ k : Set A) = (fun x => ϖ ^ k • x) '' (R : Set A) := by
    ext x
    constructor
    · intro hx
      refine ⟨ϖ ^ (-k) • x, hx, ?_⟩
      simp only [smul_smul, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero, one_smul]
    · rintro ⟨y, hy, rfl⟩
      change ϖ ^ (-k) • ϖ ^ k • y ∈ R
      simpa only [smul_smul, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero, one_smul] using
        (show y ∈ R from hy)
  rw [this]
  exact hR.isCompact.image (continuous_const_smul _)

include hϖ1 in
/-- Every element lies in some `ϖ ^ (-n) R`. -/
theorem exists_mem_orderLevel_neg (x : A) : ∃ n : ℕ, x ∈ orderLevel R ϖ (-(n : ℤ)) := by
  have := IsModuleTopology.toContinuousSMul F A
  have hc : Continuous fun c : F => c • x := continuous_id.smul continuous_const
  have hR0 : (R : Set A) ∈ 𝓝 ((0 : F) • x) := by
    rw [zero_smul]; exact hR.isOpen.mem_nhds R.zero_mem
  have hev := (tendsto_pow_atTop_nhds_zero_of_valuation_lt_one hϖ1).eventually
    (hc.continuousAt.preimage_mem_nhds hR0)
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨n, ?_⟩
  rw [mem_orderLevel, neg_neg, zpow_natCast]
  exact hn

include hϖ hϖ1 in
/-- The lattices `ϖ ^ n R` form a basis of neighbourhoods of `0`. -/
theorem exists_orderLevel_subset {U : Set A} (hU : U ∈ 𝓝 (0 : A)) :
    ∃ n : ℕ, (orderLevel R ϖ n : Set A) ⊆ U := by
  have := IsModuleTopology.toContinuousSMul F A
  have hP : ∀ y ∈ (R : Set A), ∀ᶠ z : F × A in 𝓝 ((0 : F), y), z.1 • z.2 ∈ U := by
    intro y _
    have hcont : ContinuousAt (fun z : F × A => z.1 • z.2) ((0 : F), y) :=
      continuous_smul.continuousAt
    have : U ∈ 𝓝 ((fun z : F × A => z.1 • z.2) ((0 : F), y)) := by simpa using hU
    exact hcont.preimage_mem_nhds this
  have hall := hR.isCompact.eventually_forall_of_forall_eventually
    (P := fun (c : F) (y : A) => c • y ∈ U) hP
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_valuation_lt_one hϖ1).eventually hall).exists
  refine ⟨n, fun x hx => ?_⟩
  have hx' : ϖ ^ (-(n : ℤ)) • x ∈ R := hx
  have := hn _ hx'
  simpa only [smul_smul, ← zpow_natCast, ← zpow_add₀ hϖ, add_neg_cancel, zpow_zero,
    one_smul] using this

include hϖ hϖ1 in
theorem eq_zero_of_forall_mem_orderLevel [FiniteDimensional F A] {x : A}
    (hx : ∀ n : ℕ, x ∈ orderLevel R ϖ n) : x = 0 := by
  have := t2Space_of_finiteDimensional F A
  by_contra hne
  have hU : ({x}ᶜ : Set A) ∈ 𝓝 (0 : A) :=
    isOpen_compl_singleton.mem_nhds (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_orderLevel_subset hR hϖ hϖ1 hU
  exact hn (hx n) rfl

include hϖ hϖ1 in
/-- Elements of `1 + ϖ R` are units of `A` whose inverses lie in `R`. -/
theorem exists_inverse_one_add [FiniteDimensional F A] {u : A} (hu : u ∈ orderLevel R ϖ 1) :
    ∃ v ∈ R, (1 + u) * v = 1 ∧ v * (1 + u) = 1 := by
  have hinj : ∀ y : A, (1 + u) * y = 0 → y = 0 := by
    intro y hy
    have hy' : y = -(u * y) := by
      rw [add_mul, one_mul] at hy
      exact eq_neg_of_add_eq_zero_left hy
    obtain ⟨j, hj⟩ := exists_mem_orderLevel_neg hR hϖ1 y
    have hall : ∀ t : ℕ, y ∈ orderLevel R ϖ (-(j : ℤ) + t) := by
      intro t
      induction t with
      | zero => simpa using hj
      | succ t ih =>
        rw [hy']
        refine (orderLevel R ϖ _).neg_mem ?_
        have := mul_mem_orderLevel hϖ hu ih
        convert this using 2
        push_cast; ring
    refine eq_zero_of_forall_mem_orderLevel hR hϖ hϖ1 fun n => ?_
    have := hall (n + j)
    convert this using 2
    push_cast; ring
  let Lm : A →ₗ[F] A := LinearMap.mulLeft F (1 + u)
  have hLinj : Function.Injective Lm := by
    intro a b hab
    have : (1 + u) * (a - b) = 0 := by
      rw [mul_sub]; exact sub_eq_zero.mpr hab
    exact sub_eq_zero.mp (hinj _ this)
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hLinj) 1
  have hv1 : (1 + u) * v = 1 := hv
  have hv2 : v * (1 + u) = 1 := by
    have : (1 + u) * (v * (1 + u) - 1) = 0 := by
      rw [mul_sub, ← mul_assoc, hv1, one_mul, mul_one, sub_self]
    exact sub_eq_zero.mp (hinj _ this)
  refine ⟨v, ?_, hv1, hv2⟩
  have hvv : v = 1 - u * v := by
    rw [add_mul, one_mul] at hv1
    exact eq_sub_of_add_eq hv1
  obtain ⟨j, hj⟩ := exists_mem_orderLevel_neg hR hϖ1 v
  suffices h : ∀ j : ℕ, v ∈ orderLevel R ϖ (-(j : ℤ)) → v ∈ R from h j hj
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hvj
    apply ih
    rw [hvv]
    refine (orderLevel R ϖ _).sub_mem ?_ ?_
    · exact orderLevel_anti hϖ hR.smul_mem hϖ1 (by omega) (mem_orderLevel_zero.mpr R.one_mem)
    · have := mul_mem_orderLevel hϖ hu hvj
      convert this using 2
      push_cast; ring

end Topological

end Langlands.HarmonicAnalysis.UnitConjugation
