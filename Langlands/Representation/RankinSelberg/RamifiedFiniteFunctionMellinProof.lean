import Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinStatement
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.RankinSelberg.NormalizedGeneratorRegularityProof
import Langlands.Representation.RankinSelberg.RationalEvaluation
import Langlands.LocalField.Uniformizer
import Langlands.Group.GL.NormalizedCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform ramified Laurentness of scalar finite-function Mellin integrals

Proof of `RamifiedFiniteFunctionMellinStatement`. A continuous finite function
on `Fˣ` is invariant under a principal-unit group `U^b`, chosen from the
finite function alone. For a quasicharacter nontrivial on `U^b`, the twisted
integrand vanishes below some order (compact support of the test), grows at
most geometrically along powers of the uniformizer (finite-function growth),
and is multiplied by a constant different from one under a unit translation
above some order (the test is constant near zero). The abstract shell theorem
then gives absolute convergence and a finite shell sum, which is a Laurent
polynomial in the spectral point.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Topology
open Langlands.RankinSelberg.RationalEvaluation

universe uF uG

/-! ### Translation operators on finite functions

For a complex function on a topological monoid whose left translates span a
finite-dimensional space, left translation acts on that span by linear operators
depending continuously on the translating element. Some neighborhood of one then
contains no nontrivial element all of whose powers stay in it, and translates
along the powers of a fixed element grow at most geometrically, uniformly on a
compact set. -/

section FiniteFunctionTranslation



/-- No small subgroups for a complex normed ring: if all powers of `g` stay
within distance `ε < 1` of one, then `g = 1`. -/
private theorem eq_one_of_forall_norm_pow_sub_one_le {R : Type*} [NormedRing R] [NormedSpace ℂ R]
    {g : R} {ε : ℝ} (hε : ε < 1) (h : ∀ n : ℕ, ‖g ^ n - 1‖ ≤ ε) : g = 1 := by
  by_contra hg
  have hd : 0 < ‖g - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hg)
  have key (n : ℕ) : (n : ℝ) * ‖g - 1‖ ≤ ε + n * (ε * ‖g - 1‖) := by
    have hid : (n : ℂ) • (g - 1) =
        (g ^ n - 1) - ∑ k ∈ Finset.range n, (g ^ k - 1) * (g - 1) := by
      rw [Nat.cast_smul_eq_nsmul, ← geom_sum_mul g n, ← Finset.sum_mul, ← sub_mul,
        ← Finset.sum_sub_distrib]
      simp [nsmul_eq_mul]
    have h1 : ‖(n : ℂ) • (g - 1)‖ = n * ‖g - 1‖ := by
      rw [norm_smul]
      simp
    calc (n : ℝ) * ‖g - 1‖
        = ‖(g ^ n - 1) - ∑ k ∈ Finset.range n, (g ^ k - 1) * (g - 1)‖ := by
          rw [← hid, h1]
      _ ≤ ‖g ^ n - 1‖ + ‖∑ k ∈ Finset.range n, (g ^ k - 1) * (g - 1)‖ := norm_sub_le _ _
      _ ≤ ε + ∑ k ∈ Finset.range n, ‖(g ^ k - 1) * (g - 1)‖ :=
          add_le_add (h n) (norm_sum_le _ _)
      _ ≤ ε + ∑ _k ∈ Finset.range n, ε * ‖g - 1‖ := by
          gcongr with k hk
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (h k) (norm_nonneg _))
      _ = ε + n * (ε * ‖g - 1‖) := by simp
  have hpos : 0 < (1 - ε) * ‖g - 1‖ := mul_pos (by linarith) hd
  obtain ⟨n, hn⟩ := exists_nat_gt (ε / ((1 - ε) * ‖g - 1‖))
  rw [div_lt_iff₀ hpos] at hn
  have := key n
  nlinarith

variable {G : Type uG} [Monoid G]

/-- The complex span of the left translates `a ↦ η (b * a)` of a function. -/
private abbrev translationSpan (η : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun b : G => fun a : G => η (b * a))

private theorem mem_translationSpan_self (η : G → ℂ) : η ∈ translationSpan η :=
  Submodule.subset_span ⟨1, funext fun a => by simp only [one_mul]⟩

/-- The translation span is stable under every left translation. -/
private theorem translate_mem_translationSpan (η : G → ℂ) (u : G) {v : G → ℂ}
    (hv : v ∈ translationSpan η) : (fun a => v (u * a)) ∈ translationSpan η := by
  have hmap : (translationSpan η).map (LinearMap.funLeft ℂ ℂ (fun a : G => u * a)) ≤
      translationSpan η := by
    rw [Submodule.map_span_le]
    rintro _ ⟨b, rfl⟩
    exact Submodule.subset_span ⟨b * u, funext fun a => by
      simp [LinearMap.funLeft_apply, mul_assoc]⟩
  exact hmap (Submodule.mem_map_of_mem hv)

/-- Left translation by `u`, as a linear operator on the translation span. -/
private def translationOperator (η : G → ℂ) (u : G) : Module.End ℂ (translationSpan η) :=
  (LinearMap.funLeft ℂ ℂ (fun a : G => u * a)).restrict
    (fun _v hv => translate_mem_translationSpan η u hv)

@[simp]
private theorem translationOperator_apply (η : G → ℂ) (u : G) (v : translationSpan η) (a : G) :
    (translationOperator η u v : G → ℂ) a = (v : G → ℂ) (u * a) := rfl

private theorem translationOperator_one (η : G → ℂ) : translationOperator η 1 = 1 := by
  ext v a
  simp

private theorem translationOperator_mul (η : G → ℂ) (u w : G) :
    translationOperator η (u * w) = translationOperator η w * translationOperator η u := by
  ext v a
  simp [mul_assoc]

private theorem translationOperator_pow (η : G → ℂ) (u : G) (n : ℕ) :
    translationOperator η (u ^ n) = translationOperator η u ^ n := by
  induction n with
  | zero => simp [translationOperator_one]
  | succ n ih => rw [pow_succ, translationOperator_mul, ih, pow_succ']

section Coordinates

variable (η : G → ℂ) [FiniteDimensional ℂ (translationSpan η)]

/-- Coordinates on the finite-dimensional translation span. -/
private def coord :
    translationSpan η ≃ₗ[ℂ] (Fin (Module.finrank ℂ (translationSpan η)) → ℂ) :=
  (Module.finBasis ℂ (translationSpan η)).equivFun

/-- Left translation in coordinates, as a continuous operator. -/
private def coordOperator (u : G) :
    (Fin (Module.finrank ℂ (translationSpan η)) → ℂ) →L[ℂ]
      (Fin (Module.finrank ℂ (translationSpan η)) → ℂ) :=
  LinearMap.toContinuousLinearMap
    ((coord η).toLinearMap ∘ₗ translationOperator η u ∘ₗ (coord η).symm.toLinearMap)

private theorem coordOperator_apply_coord (u : G) (v : translationSpan η) :
    coordOperator η u (coord η v) = coord η (translationOperator η u v) := by
  simp [coordOperator]

private theorem coordOperator_one : coordOperator η 1 = 1 := by
  ext1 y
  simp [coordOperator, translationOperator_one]

private theorem coordOperator_pow (u : G) (n : ℕ) :
    coordOperator η (u ^ n) = coordOperator η u ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, coordOperator_one]
  | succ n ih =>
    rw [pow_succ' u n, pow_succ (coordOperator η u) n, ← ih]
    ext1 y
    simp [coordOperator, translationOperator_mul]

end Coordinates

variable [TopologicalSpace G] [ContinuousMul G]

/-- Every element of the translation span of a continuous function is continuous. -/
private theorem continuous_of_mem_translationSpan {η : G → ℂ} (hη : Continuous η) {v : G → ℂ}
    (hv : v ∈ translationSpan η) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨b, rfl⟩ := hv
    exact hη.comp (continuous_const.mul continuous_id)
  | zero => exact continuous_const
  | add v w _ _ hv hw => exact hv.add hw
  | smul c v _ hv => exact hv.const_smul c

private theorem continuous_coordOperator (η : G → ℂ) [FiniteDimensional ℂ (translationSpan η)]
    (hη : Continuous η) : Continuous (coordOperator η) := by
  apply continuous_clm_apply.mpr
  intro y
  have hτ : Continuous fun u : G => translationOperator η u ((coord η).symm y) := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro a
    exact (continuous_of_mem_translationSpan hη ((coord η).symm y).2).comp
      (continuous_id.mul continuous_const)
  exact (coord η).toLinearMap.continuous_of_finiteDimensional.comp hτ

/-- A continuous finite function is invariant under every element of a fixed
neighborhood of one all of whose powers remain in that neighborhood. -/
private theorem exists_nhds_translation_invariant {η : G → ℂ} (hη : Continuous η)
    (hfin : FiniteDimensional ℂ (translationSpan η)) :
    ∃ W ∈ 𝓝 (1 : G), ∀ u : G, (∀ n : ℕ, u ^ n ∈ W) → ∀ a : G, η (u * a) = η a := by
  let A := coordOperator η
  have hA := continuous_coordOperator η hη
  refine ⟨{u | ‖A u - 1‖ < 1 / 2}, ?_, ?_⟩
  · apply (isOpen_lt (hA.sub continuous_const).norm continuous_const).mem_nhds
    simp [coordOperator_one]
  · intro u hu a
    have hA1 : A u = 1 := by
      apply eq_one_of_forall_norm_pow_sub_one_le (ε := 1 / 2) (by norm_num)
      intro n
      have := hu n
      simp only [Set.mem_ofPred_eq, A, coordOperator_pow] at this
      exact this.le
    have hτ : translationOperator η u ⟨η, mem_translationSpan_self η⟩ =
        ⟨η, mem_translationSpan_self η⟩ := by
      apply (coord η).injective
      rw [← coordOperator_apply_coord]
      change A u _ = _
      rw [hA1]; rfl
    simpa using congrFun (congrArg Subtype.val hτ) a

/-- Translates of a continuous finite function along the powers of `g` grow at
most geometrically, uniformly on a compact set. -/
private theorem exists_translation_pow_bound {η : G → ℂ} (hη : Continuous η)
    (hfin : FiniteDimensional ℂ (translationSpan η)) (g : G) {K : Set G}
    (hK : IsCompact K) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ ∀ n : ℕ, ∀ a ∈ K, ‖η (g ^ n * a)‖ ≤ C * r ^ n := by
  let A := coordOperator η g
  let B := Module.finBasis ℂ (translationSpan η)
  have hbound (i : Fin (Module.finrank ℂ (translationSpan η))) :
      ∃ M : ℝ, ∀ a ∈ K, ‖((B i : translationSpan η) : G → ℂ) a‖ ≤ M :=
    hK.exists_bound_of_continuousOn
      (continuous_of_mem_translationSpan hη (B i).2).norm.continuousOn |>.imp
      fun M hM a ha => by simpa using hM a ha
  choose M hM using hbound
  set S := ∑ i, |M i| with hS_def
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  let η' : translationSpan η := ⟨η, mem_translationSpan_self η⟩
  -- Evaluation of a vector of the span through its coordinates.
  have heval (v : translationSpan η) (a : G) (ha : a ∈ K) :
      ‖(v : G → ℂ) a‖ ≤ ‖coord η v‖ * S := by
    have hv : (v : G → ℂ) = ∑ i, (coord η v i) • ((B i : translationSpan η) : G → ℂ) := by
      have := congrArg Subtype.val (B.sum_repr v)
      rw [Submodule.coe_sum] at this
      simpa [coord, B, Module.Basis.equivFun_apply] using this.symm
    rw [hv, Finset.sum_apply, hS_def, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul (norm_le_pi_norm (coord η v) i) ((hM i a ha).trans (le_abs_self _))
      (norm_nonneg _) (norm_nonneg _)
  have hpow (n : ℕ) (y) : ‖(A ^ n) y‖ ≤ ‖A‖ ^ n * ‖y‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp,
        pow_succ, mul_comm (‖A‖ ^ n) ‖A‖, mul_assoc]
      exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
  refine ⟨‖coord η η'‖ * S, ‖A‖, mul_nonneg (norm_nonneg _) hS, norm_nonneg _,
    fun n a ha => ?_⟩
  have hc : coord η (translationOperator η (g ^ n) η') = (A ^ n) (coord η η') := by
    rw [← coordOperator_apply_coord, coordOperator_pow]
  have := heval (translationOperator η (g ^ n) η') a ha
  rw [hc, translationOperator_apply] at this
  calc ‖η (g ^ n * a)‖ ≤ ‖(A ^ n) (coord η η')‖ * S := this
    _ ≤ ‖A‖ ^ n * ‖coord η η'‖ * S := mul_le_mul_of_nonneg_right (hpow n _) hS
    _ = ‖coord η η'‖ * S * ‖A‖ ^ n := by ring

end FiniteFunctionTranslation

/-! ### Finite shell sums for order-weighted integrals

Let `ord` be a continuous homomorphism from a measurable group to `ℤ`, with an
element `ϖ` of order one, and let `μ` be a left-invariant measure giving the
order-zero shell finite mass. For a continuous complex function `g` vanishing
below some order `R0`, growing at most geometrically along the powers of `ϖ`
above it, and multiplied by a constant `c ≠ 1` under an order-zero translation
from some order `N` on, the weighted integral `∫ g a * z ^ ord a` converges
absolutely for every small nonzero `z` and equals the finite shell sum over the
orders in `[R0, N)`. -/

section OrderShellSum

open Set


namespace OrderShell

variable {G : Type*} [Group G] {ord : G → ℤ}

private theorem ord_one (hmul : ∀ a b, ord (a * b) = ord a + ord b) : ord 1 = 0 := by
  have h := hmul 1 1
  rw [one_mul] at h
  linarith

private theorem ord_inv (hmul : ∀ a b, ord (a * b) = ord a + ord b) (a : G) : ord a⁻¹ = -ord a := by
  have h := hmul a⁻¹ a
  rw [inv_mul_cancel, ord_one hmul] at h
  linarith

private theorem ord_pow (hmul : ∀ a b, ord (a * b) = ord a + ord b) (a : G) (n : ℕ) :
    ord (a ^ n) = n * ord a := by
  induction n with
  | zero => simp [ord_one hmul]
  | succ n ih => rw [pow_succ, hmul, ih]; push_cast; ring

private theorem ord_zpow (hmul : ∀ a b, ord (a * b) = ord a + ord b) (a : G) (n : ℤ) :
    ord (a ^ n) = n * ord a := by
  cases n with
  | ofNat n => simp [ord_pow hmul]
  | negSucc n =>
    rw [zpow_negSucc, ord_inv hmul, ord_pow hmul, Int.negSucc_eq]
    push_cast
    ring

variable [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]

/-- The weighted integral of a function vanishing below order `R0`, with
geometric growth above it and translation cancellation from order `N` on,
is the finite shell sum over `[R0, N)` for all small nonzero `z`. -/
private theorem exists_integral_eq_shell_sum (μ : Measure G) [μ.IsMulLeftInvariant]
    (hmul : ∀ a b, ord (a * b) = ord a + ord b) (hord : Continuous ord)
    {ϖ : G} (hϖ : ord ϖ = 1) (hmass : μ {a | ord a = 0} ≠ ⊤)
    {g : G → ℂ} (hg : Continuous g) {R0 : ℤ} (hR0 : ∀ a, ord a < R0 → g a = 0)
    {C r : ℝ} (hr : 0 ≤ r) (hgrowth : ∀ j : ℕ, ∀ k, ord k = R0 → ‖g (ϖ ^ j * k)‖ ≤ C * r ^ j)
    {N : ℤ} {u : G} {c : ℂ} (hu : ord u = 0) (hc : c ≠ 1)
    (htail : ∀ a, N ≤ ord a → g (u * a) = c * g a) :
    ∃ ρ > 0, ∀ z : ℂ, z ≠ 0 → ‖z‖ < ρ →
      Integrable (fun a => g a * z ^ ord a) μ ∧
      ∫ a, g a * z ^ ord a ∂μ =
        ∑ n ∈ Finset.Ico R0 N, (∫ a in {a | ord a = n}, g a ∂μ) * z ^ n := by
  set S : ℤ → Set G := fun n => {a | ord a = n} with hS
  have hSm (n : ℤ) : MeasurableSet (S n) :=
    ((isOpen_discrete ({n} : Set ℤ)).preimage hord).measurableSet
  have hSμ (n : ℤ) : μ (S n) = μ (S 0) := by
    have hpre : S n = (fun h => ϖ ^ (-n) * h) ⁻¹' S 0 := by
      ext a
      change ord a = n ↔ ord (ϖ ^ (-n) * a) = 0
      rw [hmul, ord_zpow hmul, hϖ]
      omega
    rw [hpre, measure_preimage_mul]
  have hSfin (n : ℤ) : μ (S n) ≠ ⊤ := by rw [hSμ n]; exact hmass
  -- Geometric bound on the shells above `R0`.
  have hbound (j : ℕ) (a : G) (ha : ord a = R0 + j) : ‖g a‖ ≤ C * r ^ j := by
    have hk : ord ((ϖ ^ j)⁻¹ * a) = R0 := by
      rw [hmul, ord_inv hmul, ord_pow hmul, hϖ, ha]
      ring
    simpa [mul_inv_cancel_left] using hgrowth j _ hk
  have hlow (n : ℤ) (hn : n < R0) (a : G) (ha : a ∈ S n) : g a = 0 :=
    hR0 a (by rw [show ord a = n from ha]; exact hn)
  have hshell (n : ℤ) : ∃ M : ℝ, ∀ a ∈ S n, ‖g a‖ ≤ M := by
    by_cases hn : n < R0
    · exact ⟨0, fun a ha => by rw [hlow n hn a ha, norm_zero]⟩
    · refine ⟨C * r ^ (n - R0).toNat, fun a ha => hbound _ a ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      change ord a = n at ha
      omega
  -- Cancellation on the shells from `N` on.
  have hcancel (n : ℤ) (hn : N ≤ n) : ∫ a in S n, g a ∂μ = 0 := by
    have hind (a : G) : (S n).indicator g (u * a) = c * (S n).indicator g a := by
      by_cases ha : a ∈ S n
      · have hua : u * a ∈ S n := by
          change ord (u * a) = n
          rw [hmul, hu, zero_add]
          exact ha
        rw [indicator_of_mem hua, indicator_of_mem ha]
        exact htail a (by rw [show ord a = n from ha]; exact hn)
      · have hua : u * a ∉ S n := by
          intro hua
          apply ha
          change ord (u * a) = n at hua
          rw [hmul, hu, zero_add] at hua
          exact hua
        rw [indicator_of_notMem hua, indicator_of_notMem ha, mul_zero]
    have hI : ∫ a in S n, g a ∂μ = c * ∫ a in S n, g a ∂μ :=
      calc ∫ a in S n, g a ∂μ = ∫ a, (S n).indicator g a ∂μ :=
            (integral_indicator (hSm n)).symm
        _ = ∫ a, (S n).indicator g (u * a) ∂μ := (integral_mul_left_eq_self _ u).symm
        _ = ∫ a, c * (S n).indicator g a ∂μ := by simp_rw [hind]
        _ = c * ∫ a in S n, g a ∂μ := by rw [integral_const_mul, integral_indicator (hSm n)]
    have h1 : (1 - c) * ∫ a in S n, g a ∂μ = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hc.symm)
  refine ⟨1 / (r + 1), by positivity, fun z hz hzρ => ?_⟩
  have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hrz : r * ‖z‖ < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hzρ
    nlinarith [norm_nonneg z]
  set F : G → ℂ := fun a => g a * z ^ ord a with hF
  have hFc : Continuous F :=
    hg.mul ((continuous_of_discreteTopology (f := fun n : ℤ => z ^ n)).comp hord)
  have hFnorm (n : ℤ) (a : G) (ha : a ∈ S n) : ‖F a‖ = ‖g a‖ * ‖z‖ ^ n := by
    rw [hF, norm_mul, norm_zpow, show ord a = n from ha]
  have hFi (n : ℤ) : IntegrableOn F (S n) μ := by
    obtain ⟨M, hM⟩ := hshell n
    refine Measure.integrableOn_of_bounded (M := M * ‖z‖ ^ n) (hSfin n)
      hFc.aestronglyMeasurable (ae_restrict_of_forall_mem (hSm n) fun a ha => ?_)
    rw [hFnorm n a ha]
    exact mul_le_mul_of_nonneg_right (hM a ha) (zpow_nonneg (norm_nonneg z) n)
  -- Summability of the shell norm integrals.
  have hsum : Summable fun n : ℤ => ∫ a in S n, ‖F a‖ ∂μ := by
    have hinj : Function.Injective fun j : ℕ => R0 + (j : ℤ) := fun i j h => by
      simpa using h
    refine (hinj.summable_iff fun n hn => ?_).mp ?_
    · have hlt : n < R0 := by
        by_contra hge
        exact hn ⟨(n - R0).toNat, by simp only; rw [Int.toNat_of_nonneg (by omega)]; ring⟩
      exact setIntegral_eq_zero_of_forall_eq_zero fun a ha => by
        rw [hF]; simp [hlow n hlt a ha]
    · refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun a => norm_nonneg _)
        (fun j => ?_) ((summable_geometric_of_lt_one (by positivity) hrz).mul_left
          (C * ‖z‖ ^ R0 * μ.real (S 0)))
      have hle : ∫ a in S (R0 + j), ‖F a‖ ∂μ ≤
          (C * r ^ j * ‖z‖ ^ (R0 + (j : ℤ))) * μ.real (S (R0 + j)) := by
        refine (Real.le_norm_self _).trans
          (norm_setIntegral_le_of_norm_le_const (hSfin _).lt_top fun a ha => ?_)
        rw [norm_norm, hFnorm _ a ha]
        exact mul_le_mul_of_nonneg_right (hbound j a ha) (zpow_nonneg (norm_nonneg z) _)
      refine hle.trans (le_of_eq ?_)
      rw [Measure.real, Measure.real, hSμ (R0 + j), zpow_add₀ hz0, zpow_natCast, mul_pow]
      ring
  have hU : (⋃ n, S n) = univ :=
    eq_univ_of_forall fun a => mem_iUnion.mpr ⟨ord a, rfl⟩
  have hint : Integrable F μ := by
    have := integrableOn_iUnion_of_summable_integral_norm hFi hsum
    rwa [hU, integrableOn_univ] at this
  refine ⟨hint, ?_⟩
  have hdisj : Pairwise (Function.onFun Disjoint S) := fun m n hmn =>
    disjoint_left.mpr fun a ha hb => hmn ((show ord a = m from ha).symm.trans hb)
  have hterm (n : ℤ) : ∫ a in S n, F a ∂μ = (∫ a in S n, g a ∂μ) * z ^ n := by
    rw [← integral_mul_const]
    exact setIntegral_congr_fun (hSm n) fun a ha => by
      rw [hF]; simp only; rw [show ord a = n from ha]
  have hall : ∫ a, F a ∂μ = ∑' n, ∫ a in S n, F a ∂μ := by
    rw [← integral_iUnion hSm hdisj (by rw [hU]; exact hint.integrableOn), hU,
      Measure.restrict_univ]
  rw [hall, tsum_congr hterm]
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hn
  rcases hn with hn | hn
  · rw [setIntegral_eq_zero_of_forall_eq_zero fun a ha => hlow n hn a ha, zero_mul]
  · rw [hcancel n hn, zero_mul]

end OrderShell

end OrderShellSum

/-! ### The ramified Mellin integrals -/

section LocalFieldFacts

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private theorem localField_t2' (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

/-- On units the discrete valuation is the exponential of minus the order. -/
private theorem discreteValuation_units (T : F.TopologicalData) (a : F.Carrierˣ) :
    T.discreteValuation (a : F.Carrier) = WithZero.exp (-T.ord (a : F.Carrier)) := by
  have h0 : T.discreteValuation (a : F.Carrier) ≠ 0 :=
    (T.discreteValuation.ne_zero_iff).mpr a.ne_zero
  rw [PadicField.TopologicalData.ord, neg_neg, WithZero.exp_log h0]

/-- The order-zero units are exactly the units of the integer ring. -/
private theorem ord_eq_zero_iff_mem_integralUnits (T : F.TopologicalData) (a : F.Carrierˣ) :
    T.ord (a : F.Carrier) = 0 ↔ a ∈ integralUnits T.Integers := by
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  rw [mem_integralUnits, ← T.normalizedAbs_le_one_iff_mem_integers,
    ← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_of_ne_zero a.ne_zero,
    T.normalizedAbs_of_ne_zero (a⁻¹).ne_zero, Units.val_inv_eq_inv_val, T.ord_inv,
    zpow_le_one_iff_right₀ hq, zpow_le_one_iff_right₀ hq]
  omega

end LocalFieldFacts

/-- The weighted normalized absolute value is an integer power of the spectral
point. Positivity of `q` fixes the logarithm branch. -/
private theorem natCast_zpow_cpow_eq (q : ℕ) (hq : 0 < q) (k : ℤ) (m : ℕ) (s : ℂ) :
    ((((q : ℝ) ^ (-k) : ℝ)) : ℂ) ^ ((m : ℂ) * s) = (spectralPoint q s ^ m) ^ k := by
  have harg : Complex.arg (q : ℂ) = 0 := by
    simpa only [Complex.ofReal_natCast] using
      Complex.arg_ofReal_of_nonneg (show 0 ≤ (q : ℝ) by positivity)
  rw [Complex.ofReal_zpow, Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [harg, Real.pi_pos])
      (by simpa only [harg, mul_zero] using Real.pi_pos.le),
    spectralPoint, ← zpow_natCast, ← zpow_mul, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

private theorem spectralPoint_ne_zero' {q : ℕ} (hq : 1 < q) (s : ℂ) :
    spectralPoint q s ≠ 0 := by
  intro h
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact hq0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- Positive powers of the spectral point are small on a right half-plane. -/
private theorem exists_re_threshold {q : ℕ} (hq : 1 < q) {m : ℕ} (hm : 0 < m) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ c : ℝ, ∀ s : ℂ, c < s.re → ‖spectralPoint q s ^ m‖ < ρ := by
  set ρ1 := min ρ 1 with hρ1_def
  have hρ1 : 0 < ρ1 := lt_min hρ one_pos
  have hq0 : 0 < q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine ⟨-Real.log ρ1 / Real.log q, fun s hs => ?_⟩
  have hnorm : ‖spectralPoint q s‖ = (q : ℝ) ^ (-s.re) := by
    rw [spectralPoint, Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re]
  have ht : (q : ℝ) ^ (-s.re) < ρ1 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hq0), ← Real.lt_log_iff_exp_lt hρ1]
    rw [div_lt_iff₀ hlogq] at hs
    linarith
  have ht0 : 0 ≤ (q : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  rw [norm_pow, hnorm]
  calc ((q : ℝ) ^ (-s.re)) ^ m ≤ (q : ℝ) ^ (-s.re) :=
        pow_le_of_le_one ht0 (ht.le.trans (min_le_right _ _)) hm.ne'
    _ < ρ1 := ht
    _ ≤ ρ := min_le_left _ _

/-- Evaluation of the rational image of a finite Laurent sum at a nonzero point. -/
private theorem eval_laurentToRatFunc_sum {w : ℂ} (hw : w ≠ 0) (S : Finset ℤ) (d : ℤ → ℂ)
    (e : ℤ → ℤ) :
    RatFunc.eval (RingHom.id ℂ) w (laurentToRatFunc
      (∑ n ∈ S, LaurentPolynomial.C (d n) * LaurentPolynomial.T (e n))) =
      ∑ n ∈ S, d n * w ^ (e n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert n S hn ih =>
    rw [Finset.sum_insert hn, Finset.sum_insert hn, map_add,
      eval_add (regularAt_laurentToRatFunc _ hw) (regularAt_laurentToRatFunc _ hw), ih,
      map_mul, eval_mul (regularAt_laurentToRatFunc _ hw) (regularAt_laurentToRatFunc _ hw),
      laurentToRatFunc_T, eval_zpow (by simpa using hw), RatFunc.eval_X]
    rw [show laurentToRatFunc (LaurentPolynomial.C (d n)) = RatFunc.C (d n) from
      LaurentPolynomial.eval₂_C _ _ _, RatFunc.eval_C]
    rfl

/-- A continuous finite function on the units of a `p`-adic field has one
principal-unit level beyond which every sufficiently ramified twist has
convergent Mellin integrals with Laurent polynomial continuation. -/
theorem ramifiedFiniteFunctionMellin : RamifiedFiniteFunctionMellinStatement.{uF} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  have := localField_t2' F.Carrier
  intro dmu finiteFunction η hη
  obtain ⟨hηc, hηfin⟩ := hη
  have hfin : FiniteDimensional ℂ (translationSpan η) := hηfin
  obtain ⟨W, hW, hWinv⟩ := exists_nhds_translation_invariant hηc hfin
  obtain ⟨b, hb⟩ := T.exists_principalUnits_subset hW
  refine ⟨b, fun α hα m hm Φ => ?_⟩
  intro f mellin
  obtain ⟨u, hu, hαu⟩ := hα
  have hηu (a : F.Carrierˣ) : η (u * a) = η a :=
    hWinv u (fun n => hb (Subgroup.pow_mem _ hu n)) a
  -- The order map on units and the uniformizer.
  set q := T.residueCardinality with hq_def
  have hq1 : 1 < q := T.residueCardinality_gt_one
  let ord : F.Carrierˣ → ℤ := fun a => T.ord (a : F.Carrier)
  have hmul (a c : F.Carrierˣ) : ord (a * c) = ord a + ord c := by
    change T.ord ((a * c : F.Carrierˣ) : F.Carrier) = _
    rw [Units.val_mul]
    exact T.ord_mul a.ne_zero c.ne_zero
  have hordc : Continuous ord := continuous_ord_units T
  let ϖ : F.Carrierˣ := LocalFactor.PadicAbelian.uniformizerUnit T
  have hϖ : ord ϖ = 1 := LocalFactor.PadicAbelian.uniformizerUnit_ord T
  have hu0 : ord u = 0 := by
    have h1 := ((T.mem_principalUnits b u).mp hu).1
    change -WithZero.log (T.discreteValuation (u : F.Carrier)) = 0
    rw [h1, WithZero.log_one, neg_zero]
  -- The order-zero shell is the compact group of integral units, of mass one.
  have hS0eq : {a : F.Carrierˣ | ord a = 0} =
      (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) :=
    Set.ext fun a => ord_eq_zero_iff_mem_integralUnits T a
  have hS0 : IsCompact {a : F.Carrierˣ | ord a = 0} := by
    rw [hS0eq]
    exact integralUnits_isCompact _
  have hmass : dmu {a | ord a = 0} ≠ ⊤ := by
    have h1 : dmu (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) =
        1 := localMultiplicativeHaar_integerUnits F.Carrier
    rw [hS0eq, h1]
    exact ENNReal.one_ne_top
  -- The twisted function.
  let g : F.Carrierˣ → ℂ := fun a => Φ (a : F.Carrier) * η a * (α a : ℂ)
  have hαc : Continuous fun a : F.Carrierˣ => (α a : ℂ) :=
    Units.continuous_val.comp α.continuous
  have hgc : Continuous g :=
    ((Φ.continuous.comp Units.continuous_val).mul hηc).mul hαc
  -- Compact support of the test bounds the order from below.
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℤ, ∀ a : F.Carrierˣ, ord a < R0 → g a = 0 := by
    have habs : Continuous fun x : F.Carrier => T.normalizedAbs x :=
      NNReal.continuous_coe.comp T.continuous_normalizedAbsHom
    obtain ⟨M, hM⟩ :=
      Φ.hasCompactSupport.isCompact.exists_bound_of_continuousOn habs.continuousOn
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M (show (1 : ℝ) < q by exact_mod_cast hq1)
    refine ⟨-(k : ℤ), fun a ha => ?_⟩
    by_contra hga
    have hΦ : Φ (a : F.Carrier) ≠ 0 := fun h => hga (by simp [g, h])
    have h1 := hM _ (subset_tsupport _ (Function.mem_support.mpr hΦ))
    rw [Real.norm_of_nonneg (T.normalizedAbs_nonneg _),
      T.normalizedAbs_of_ne_zero a.ne_zero] at h1
    have h2 : (q : ℝ) ^ (k : ℤ) < (q : ℝ) ^ (-T.ord (a : F.Carrier)) :=
      zpow_lt_zpow_right₀ (by exact_mod_cast hq1)
        (by change T.ord (a : F.Carrier) < -(k : ℤ) at ha; omega)
    rw [zpow_natCast] at h2
    linarith
  -- Geometric growth along the powers of the uniformizer.
  have hK : IsCompact {a : F.Carrierˣ | ord a = R0} := by
    have hKeq : {a : F.Carrierˣ | ord a = R0} =
        (fun x => ϖ ^ R0 * x) '' {a : F.Carrierˣ | ord a = 0} := by
      ext a
      constructor
      · intro ha
        refine ⟨ϖ ^ (-R0) * a, ?_, ?_⟩
        · change ord (ϖ ^ (-R0) * a) = 0
          rw [hmul, OrderShell.ord_zpow hmul, hϖ]
          change ord a = R0 at ha
          omega
        · change ϖ ^ R0 * (ϖ ^ (-R0) * a) = a
          rw [zpow_neg, mul_inv_cancel_left]
      · rintro ⟨x, hx, rfl⟩
        change ord (ϖ ^ R0 * x) = R0
        rw [hmul, OrderShell.ord_zpow hmul, hϖ]
        change ord x = 0 at hx
        omega
    rw [hKeq]
    exact hS0.image (continuous_const.mul continuous_id)
  obtain ⟨C, r, hr, hgrowth⟩ : ∃ C r : ℝ, 0 ≤ r ∧
      ∀ j : ℕ, ∀ k, ord k = R0 → ‖g (ϖ ^ j * k)‖ ≤ C * r ^ j := by
    obtain ⟨Cη, rη, hCη, hrη, hηbd⟩ := exists_translation_pow_bound hηc hfin ϖ hK
    obtain ⟨MΦ, hMΦ⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
    have hMΦ0 : 0 ≤ MΦ := (norm_nonneg _).trans (hMΦ 0)
    obtain ⟨Mα, hMα⟩ := hK.exists_bound_of_continuousOn hαc.continuousOn
    refine ⟨MΦ * Cη * max Mα 0, rη * ‖(α ϖ : ℂ)‖, mul_nonneg hrη (norm_nonneg _),
      fun j k hk => ?_⟩
    have hαk : ‖(α k : ℂ)‖ ≤ max Mα 0 := (hMα k hk).trans (le_max_left _ _)
    have h1 : ‖Φ ((ϖ ^ j * k : F.Carrierˣ) : F.Carrier)‖ * ‖η (ϖ ^ j * k)‖ ≤
        MΦ * (Cη * rη ^ j) :=
      mul_le_mul (hMΦ _) (hηbd j k hk) (norm_nonneg _) hMΦ0
    have h2 : ‖(α (ϖ ^ j * k) : ℂ)‖ ≤ ‖(α ϖ : ℂ)‖ ^ j * max Mα 0 := by
      rw [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left hαk (pow_nonneg (norm_nonneg _) _)
    calc ‖g (ϖ ^ j * k)‖ = ‖Φ ((ϖ ^ j * k : F.Carrierˣ) : F.Carrier)‖ *
          ‖η (ϖ ^ j * k)‖ * ‖(α (ϖ ^ j * k) : ℂ)‖ := by
          simp only [g, norm_mul]
      _ ≤ (MΦ * (Cη * rη ^ j)) * (‖(α ϖ : ℂ)‖ ^ j * max Mα 0) :=
          mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg hMΦ0 (mul_nonneg hCη (pow_nonneg hrη _)))
      _ = MΦ * Cη * max Mα 0 * (rη * ‖(α ϖ : ℂ)‖) ^ j := by rw [mul_pow]; ring
  -- The test is constant near zero, so translation by `u` multiplies by `α u`.
  obtain ⟨N, htail⟩ : ∃ N : ℤ, ∀ a, N ≤ ord a → g (u * a) = (α u : ℂ) * g a := by
    have hnhds : (Φ : F.Carrier → ℂ) ⁻¹' {Φ 0} ∈ 𝓝 (0 : F.Carrier) :=
      (Φ.locallyConstant.isOpen_fiber _).mem_nhds rfl
    obtain ⟨k, hk⟩ := T.exists_additiveLattice_subset hnhds
    have hΦ (a : F.Carrierˣ) (ha : -k ≤ ord a) : Φ (a : F.Carrier) = Φ 0 := by
      have hmem : (a : F.Carrier) ∈ (T.additiveLattice k : Set F.Carrier) := by
        rw [SetLike.mem_coe, T.mem_additiveLattice, discreteValuation_units T a]
        exact WithZero.exp_le_exp.mpr (by change -k ≤ T.ord (a : F.Carrier) at ha; omega)
      exact hk hmem
    refine ⟨-k, fun a ha => ?_⟩
    have hua : -k ≤ ord (u * a) := by rw [hmul, hu0, zero_add]; exact ha
    change Φ ((u * a : F.Carrierˣ) : F.Carrier) * η (u * a) * (α (u * a) : ℂ) =
      (α u : ℂ) * (Φ (a : F.Carrier) * η a * (α a : ℂ))
    rw [hΦ _ hua, hΦ _ ha, hηu, map_mul, Units.val_mul]
    ring
  have hc : (α u : ℂ) ≠ 1 := fun h => hαu (Units.ext h)
  obtain ⟨ρ, hρ, hshell⟩ := OrderShell.exists_integral_eq_shell_sum dmu hmul hordc hϖ hmass
    hgc hR0 hr hgrowth hu0 hc htail
  -- Rewrite the Mellin integrand in the spectral variable.
  have hfg (s : ℂ) (a : F.Carrierˣ) : f s a = g a * (spectralPoint q s ^ m) ^ ord a := by
    change Φ (a : F.Carrier) * η a * (α a : ℂ) *
      (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s) = _
    rw [T.normalizedAbs_of_ne_zero a.ne_zero, natCast_zpow_cpow_eq q (by omega)]
  obtain ⟨c0, hc0⟩ := exists_re_threshold hq1 hm hρ
  have hz0 (s : ℂ) : spectralPoint q s ^ m ≠ 0 := pow_ne_zero _ (spectralPoint_ne_zero' hq1 s)
  let d : ℤ → ℂ := fun n => ∫ a in {a | ord a = n}, g a ∂dmu
  refine ⟨⟨c0, fun s hs => ?_⟩,
    ⟨∑ n ∈ Finset.Ico R0 N, LaurentPolynomial.C (d n) * LaurentPolynomial.T ((m : ℤ) * n),
      c0, fun s hs => ⟨regularAt_laurentToRatFunc _ (spectralPoint_ne_zero' hq1 s), ?_⟩⟩⟩
  · have hfs : f s = fun a => g a * (spectralPoint q s ^ m) ^ ord a := funext (hfg s)
    rw [hfs]
    exact (hshell _ (hz0 s) (hc0 s hs)).1
  · change ∫ a, f s a ∂dmu = _
    simp_rw [hfg s]
    rw [(hshell _ (hz0 s) (hc0 s hs)).2,
      eval_laurentToRatFunc_sum (spectralPoint_ne_zero' hq1 s)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← zpow_natCast, ← zpow_mul]

end Langlands.RankinSelberg
