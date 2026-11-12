import Langlands.Representation.GodementJacquet.LocalTateHaar
import Langlands.Representation.GodementJacquet.TateScalarMellin
import Langlands.Representation.RankinSelberg.ValuationShellIntegrationProof
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Shell expansion of scalar Mellin integrals over a local field -/

noncomputable section

namespace Langlands.GodementJacquet.LocalTate

open MeasureTheory HarmonicAnalysis Topology ValuativeRel Conductor RankinSelberg Polynomial
open GeneralLinear.Iwasawa
open scoped ENNReal NNReal

universe uF

/-- The weighted normalized absolute value of `ϖ ^ k` is a power of the spectral point. -/
theorem natCast_zpow_cpow_eq (q : ℕ) (hq : 0 < q) (k : ℤ) (s : ℂ) :
    ((((q : ℝ) ^ (-k) : ℝ)) : ℂ) ^ (((1 : ℕ) : ℂ) * s) = spectralPoint q s ^ k := by
  have harg : Complex.arg (q : ℂ) = 0 := by
    simpa only [Complex.ofReal_natCast] using
      Complex.arg_ofReal_of_nonneg (show 0 ≤ (q : ℝ) by positivity)
  rw [Complex.ofReal_zpow, Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [harg, Real.pi_pos])
      (by simpa only [harg, mul_zero] using Real.pi_pos.le),
    spectralPoint, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : Normalization F)

section Support

/-- Every Schwartz--Bruhat function vanishes outside some lattice. -/
theorem exists_eq_zero_of_notMem_ball (f : SchwartzBruhat F) :
    ∃ A : ℤ, ∀ x, x ∉ N.ball A → f x = 0 := by
  classical
  obtain ⟨m, S, hS⟩ := N.exists_coset_expansion f
  obtain ⟨M, hM⟩ := Finset.exists_le (insert (-m) (S.image fun x0 => -N.ord x0))
  refine ⟨-M, fun x hx => ?_⟩
  rw [hS x]
  refine Finset.sum_eq_zero fun x0 hx0 => ?_
  rw [cosetIndicator_apply, Set.indicator_of_notMem, mul_zero]
  intro hmem
  apply hx
  have hmM : -M ≤ m := by
    have := hM (-m) (Finset.mem_insert_self _ _)
    omega
  have hx0M : x0 ∈ N.ball (-M) := by
    by_cases h0 : x0 = 0
    · rw [h0]
      exact zero_mem _
    · have := hM (-N.ord x0) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx0))
      exact N.ball_antitone (by omega) (N.mem_ball_ord h0)
  have := (N.ball (-M)).add_mem (N.ball_antitone hmM hmem) hx0M
  rwa [sub_add_cancel] at this

/-- Every Schwartz--Bruhat function is constant on some lattice. -/
theorem exists_eq_const_on_ball (f : SchwartzBruhat F) :
    ∃ M : ℤ, ∀ x ∈ N.ball M, f x = f 0 := by
  obtain ⟨M, hM⟩ := N.exists_ball_invariant f
  exact ⟨M, fun x hx => by simpa using hM 0 x hx⟩

/-- Both lattice bounds at once, with `A ≤ M`. -/
theorem exists_support_bounds (f : SchwartzBruhat F) :
    ∃ A M : ℤ, A ≤ M ∧ (∀ x, x ∉ N.ball A → f x = 0) ∧ ∀ x ∈ N.ball M, f x = f 0 := by
  obtain ⟨A, hA⟩ := N.exists_eq_zero_of_notMem_ball f
  obtain ⟨M, hM⟩ := N.exists_eq_const_on_ball f
  exact ⟨A, max A M, le_max_left A M, hA,
    fun x hx => hM x (N.ball_antitone (le_max_right A M) hx)⟩

end Support

section Shells

/-- The units of order `k`. -/
def ordShell (k : ℤ) : Set Fˣ := {x | N.ord (x : F) = k}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_integralUnits_iff_mem_ordShell (k : ℤ) (u : Fˣ) :
    u ∈ (integralUnits (valuation F).integer : Set Fˣ) ↔ N.ϖ ^ k * u ∈ N.ordShell k := by
  change u ∈ integralUnits (valuation F).integer ↔ N.ord ((N.ϖ ^ k * u : Fˣ) : F) = k
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val,
    N.ord_mul (zpow_ne_zero _ N.ϖ.ne_zero) u.ne_zero, N.ord_zpow_ϖ, mem_integralUnits_iff,
    ← N.ord_eq_zero_iff u.ne_zero]
  omega

theorem isOpen_ordShell (k : ℤ) : IsOpen (N.ordShell k) :=
  (isOpen_discrete ({k} : Set ℤ)).preimage N.continuous_ord_units

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem ordShell_eq_image (k : ℤ) :
    N.ordShell k = (fun u => N.ϖ ^ k * u) '' (integralUnits (valuation F).integer : Set Fˣ) := by
  ext x
  constructor
  · intro hx
    refine ⟨(N.ϖ ^ k)⁻¹ * x, (N.mem_integralUnits_iff_mem_ordShell k _).mpr ?_,
      mul_inv_cancel_left _ _⟩
    rwa [mul_inv_cancel_left]
  · rintro ⟨u, hu, rfl⟩
    exact (N.mem_integralUnits_iff_mem_ordShell k u).mp hu

theorem isCompact_ordShell (k : ℤ) : IsCompact (N.ordShell k) := by
  rw [N.ordShell_eq_image]
  exact isCompact_integralUnits.image (continuous_const.mul continuous_id)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem abv_of_mem_ordShell {k : ℤ} {x : Fˣ} (hx : x ∈ N.ordShell k) :
    N.abv (x : F) = (N.q : ℝ) ^ (-k) := by
  rw [N.abv_eq x.ne_zero, show N.ord (x : F) = k from hx]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_ordShell_of_mem_ball {x : Fˣ} {A : ℤ} (hx : (x : F) ∈ N.ball A) :
    ∃ n : ℕ, x ∈ N.ordShell (A + n) := by
  rw [N.mem_ball_iff_ord x.ne_zero] at hx
  refine ⟨(N.ord (x : F) - A).toNat, ?_⟩
  change N.ord (x : F) = A + ((N.ord (x : F) - A).toNat : ℤ)
  omega

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem pairwise_disjoint_ordShell (A : ℤ) :
    Pairwise (Function.onFun Disjoint fun n : ℕ => N.ordShell (A + n)) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun x hm hn => hmn ?_
  have h1 : N.ord (x : F) = A + m := hm
  have h2 : N.ord (x : F) = A + n := hn
  omega

end Shells

variable [MeasurableSpace Fˣ] [BorelSpace Fˣ]

section Mellin

/-- The shell coefficient `∫_{O^×} Φ(ϖ ^ k u) η(u) d^×u`. -/
def shellCoeff (η : Fˣ →* ℂˣ) (Φ : F → ℂ) (k : ℤ) : ℂ :=
  ∫ u in (integralUnits (valuation F).integer : Set Fˣ),
    Φ ((N.ϖ : F) ^ k * u) * (η u : ℂ) ∂localMultiplicativeHaar F

theorem measurableSet_ordShell (k : ℤ) : MeasurableSet (N.ordShell k) :=
  (N.isOpen_ordShell k).measurableSet

omit [MeasurableSpace Fˣ] [BorelSpace Fˣ] in
/-- The Mellin integrand on the shell of order `k`. -/
theorem mellinIntegrand_mul_zpow (η : Fˣ →* ℂˣ) (Φ : SchwartzBruhat F) (s : ℂ) (k : ℤ)
    {u : Fˣ} (hu : u ∈ (integralUnits (valuation F).integer : Set Fˣ)) :
    scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s (N.ϖ ^ k * u) =
      ((η N.ϖ : ℂ) * spectralPoint N.q s) ^ k * (Φ ((N.ϖ : F) ^ k * u) * (η u : ℂ)) := by
  have habs := N.abv_of_mem_ordShell ((N.mem_integralUnits_iff_mem_ordShell k u).mp hu)
  simp only [scalarMellinIntegrand]
  rw [habs, natCast_zpow_cpow_eq N.q N.q_pos, map_mul, map_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, mul_zpow]
  ring

theorem setIntegral_ordShell (η : Fˣ →* ℂˣ) (Φ : SchwartzBruhat F) (s : ℂ) (k : ℤ) :
    ∫ x in N.ordShell k, scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s x
        ∂localMultiplicativeHaar F =
      ((η N.ϖ : ℂ) * spectralPoint N.q s) ^ k * N.shellCoeff η Φ k := by
  rw [← setIntegral_comp_mul_left_of_mem_iff _ _ (N.ϖ ^ k)
    isOpen_integralUnits.measurableSet (N.measurableSet_ordShell k)
    (N.mem_integralUnits_iff_mem_ordShell k), shellCoeff, ← integral_const_mul]
  exact setIntegral_congr_fun isOpen_integralUnits.measurableSet
    fun u hu => N.mellinIntegrand_mul_zpow η Φ s k hu

theorem integrableOn_ordShell (η : Fˣ →* ℂˣ) (hηc : Continuous η) (Φ : SchwartzBruhat F)
    (s : ℂ) (k : ℤ) :
    IntegrableOn (scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s) (N.ordShell k)
      (localMultiplicativeHaar F) := by
  have hg : Continuous fun x : Fˣ =>
      Φ (x : F) * (η x : ℂ) * spectralPoint N.q s ^ k :=
    ((Φ.continuous.comp Units.continuous_val).mul (Units.continuous_val.comp hηc)).mul
      continuous_const
  refine (hg.continuousOn.integrableOn_compact' (N.isCompact_ordShell k)
    (N.measurableSet_ordShell k)).congr_fun (fun x hx => ?_) (N.measurableSet_ordShell k)
  simp only [scalarMellinIntegrand]
  rw [N.abv_of_mem_ordShell hx, natCast_zpow_cpow_eq N.q N.q_pos]

theorem setIntegral_norm_ordShell_le (η : Fˣ →* ℂˣ) (Φ : SchwartzBruhat F) (s : ℂ) (k : ℤ)
    {B E : ℝ} (hB : ∀ x, ‖Φ x‖ ≤ B)
    (hE : ∀ u ∈ (integralUnits (valuation F).integer : Set Fˣ), ‖(η u : ℂ)‖ ≤ E) :
    ∫ x in N.ordShell k, ‖scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s x‖
        ∂localMultiplicativeHaar F ≤
      ‖(η N.ϖ : ℂ) * spectralPoint N.q s‖ ^ k * (B * E) := by
  rw [← setIntegral_comp_mul_left_of_mem_iff _ _ (N.ϖ ^ k)
    isOpen_integralUnits.measurableSet (N.measurableSet_ordShell k)
    (N.mem_integralUnits_iff_mem_ordShell k)]
  have hbound : ∀ u ∈ (integralUnits (valuation F).integer : Set Fˣ),
      ‖‖scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s (N.ϖ ^ k * u)‖‖ ≤
        ‖(η N.ϖ : ℂ) * spectralPoint N.q s‖ ^ k * (B * E) := by
    intro u hu
    rw [norm_norm, N.mellinIntegrand_mul_zpow η Φ s k hu, norm_mul, norm_zpow]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg (norm_nonneg _) _)
    rw [norm_mul]
    exact mul_le_mul (hB _) (hE u hu) (norm_nonneg _) hB0
  have h := norm_setIntegral_le_of_norm_le_const
    (isCompact_integralUnits.measure_lt_top (μ := localMultiplicativeHaar F)) hbound
  rw [Measure.real, localMultiplicativeHaar_integerUnits, ENNReal.toReal_one, mul_one] at h
  exact (Real.le_norm_self _).trans h

/-- **Shell expansion.** If `Φ` vanishes outside `ϖ ^ A O` and `|η(ϖ) q ^ (-s)| < 1`,
the Mellin integrand is integrable and the integral is the sum of the shell
contributions of orders `A, A + 1, …`. -/
theorem mellin_hasSum (η : Fˣ →* ℂˣ) (hηc : Continuous η) (Φ : SchwartzBruhat F) {A : ℤ}
    (hA : ∀ x, x ∉ N.ball A → Φ x = 0) {s : ℂ}
    (hs : ‖(η N.ϖ : ℂ) * spectralPoint N.q s‖ < 1) :
    Integrable (scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s)
        (localMultiplicativeHaar F) ∧
      HasSum (fun n : ℕ => ((η N.ϖ : ℂ) * spectralPoint N.q s) ^ (A + n) *
          N.shellCoeff η Φ (A + n))
        (scalarMellinIntegral N.abv (localMultiplicativeHaar F) (fun x => (η x : ℂ)) 1 Φ s) := by
  set f := scalarMellinIntegrand N.abv (fun x => (η x : ℂ)) 1 Φ s with hf
  set w : ℂ := (η N.ϖ : ℂ) * spectralPoint N.q s with hw
  have hw0 : w ≠ 0 := mul_ne_zero (η N.ϖ).ne_zero (spectralPoint_ne_zero_of_pos N.q_pos s)
  have hzero : ∀ x, x ∉ ⋃ n : ℕ, N.ordShell (A + n) → f x = 0 := by
    intro x hx
    have hxA : (x : F) ∉ N.ball A := by
      intro hmem
      obtain ⟨n, hn⟩ := N.mem_ordShell_of_mem_ball hmem
      exact hx (Set.mem_iUnion.mpr ⟨n, hn⟩)
    simp only [hf, scalarMellinIntegrand, hA _ hxA, zero_mul]
  obtain ⟨B, hB⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  obtain ⟨E, hE⟩ := isCompact_integralUnits.exists_bound_of_continuousOn
    (Units.continuous_val.comp hηc).continuousOn
  have hsum : Summable fun n : ℕ => ∫ x in N.ordShell (A + n), ‖f x‖
      ∂localMultiplicativeHaar F := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => N.setIntegral_norm_ordShell_le η Φ s (A + n) hB hE) ?_
    have hg := (summable_geometric_of_lt_one (norm_nonneg w) hs).mul_left (‖w‖ ^ A * (B * E))
    refine hg.congr fun n => ?_
    rw [zpow_add₀ (norm_ne_zero_iff.mpr hw0), zpow_natCast]
    ring
  have hint : IntegrableOn f (⋃ n : ℕ, N.ordShell (A + n)) (localMultiplicativeHaar F) :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun n => N.integrableOn_ordShell η hηc Φ s (A + n)) hsum
  refine ⟨hint.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  have h := hasSum_integral_iUnion (fun n : ℕ => N.measurableSet_ordShell (A + n))
    (N.pairwise_disjoint_ordShell A) hint
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at h
  have h' : ∀ n : ℕ, ∫ x in N.ordShell (A + n), f x ∂localMultiplicativeHaar F =
      w ^ (A + n) * N.shellCoeff η Φ (A + n) := fun n => N.setIntegral_ordShell η Φ s (A + n)
  rw [funext h'] at h
  exact h

/-- Beyond the lattice on which `Φ` is constant, the shell coefficients are those
of a multiple of the character. -/
theorem shellCoeff_of_le {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a)
    (Φ : SchwartzBruhat F) {M : ℤ} (hM : ∀ x ∈ N.ball M, Φ x = Φ 0) {k : ℤ} (hk : M ≤ k) :
    N.shellCoeff η Φ k = Φ 0 * if a = 0 then 1 else 0 := by
  rw [← N.setIntegral_integralUnits_char hη, ← integral_const_mul, shellCoeff]
  refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
  have hu0 : (u : F) ∈ N.ball 0 := by
    rw [mem_ball, mem_integralUnits_iff.mp hu, zpow_zero]
  have hmem : (N.ϖ : F) ^ k * u ∈ N.ball M :=
    N.ball_antitone (by omega) (N.mul_mem_ball (N.ϖ_zpow_mem_ball k) hu0)
  rw [hM _ hmem]

/-- The closed form of the Mellin integral for `|η(ϖ) q ^ (-s)| < 1`. -/
theorem mellin_eq {η : Fˣ →* ℂˣ} (hηc : Continuous η) {a : ℕ} (hη : N.IsUnitConductor η a)
    (Φ : SchwartzBruhat F) {A M : ℤ} (hAM : A ≤ M) (hA : ∀ x, x ∉ N.ball A → Φ x = 0)
    (hM : ∀ x ∈ N.ball M, Φ x = Φ 0) {s : ℂ}
    (hs : ‖(η N.ϖ : ℂ) * spectralPoint N.q s‖ < 1) :
    scalarMellinIntegral N.abv (localMultiplicativeHaar F) (fun x => (η x : ℂ)) 1 Φ s =
      (∑ n ∈ Finset.range (M - A).toNat,
          ((η N.ϖ : ℂ) * spectralPoint N.q s) ^ (A + n) * N.shellCoeff η Φ (A + n)) +
        Φ 0 * (if a = 0 then 1 else 0) * ((η N.ϖ : ℂ) * spectralPoint N.q s) ^ M *
          (1 - (η N.ϖ : ℂ) * spectralPoint N.q s)⁻¹ := by
  set w : ℂ := (η N.ϖ : ℂ) * spectralPoint N.q s with hw
  have hw0 : w ≠ 0 := mul_ne_zero (η N.ϖ).ne_zero (spectralPoint_ne_zero_of_pos N.q_pos s)
  set n0 := (M - A).toNat with hn0
  have hn0' : A + (n0 : ℤ) = M := by omega
  set g : ℕ → ℂ := fun n => w ^ (A + n) * N.shellCoeff η Φ (A + n) with hg
  have htail : HasSum (fun n : ℕ => g (n + n0))
      (Φ 0 * (if a = 0 then 1 else 0) * w ^ M * (1 - w)⁻¹) := by
    have hgeom := (hasSum_geometric_of_norm_lt_one hs).mul_left
      (Φ 0 * (if a = 0 then 1 else 0) * w ^ M)
    refine hgeom.congr_fun fun n => ?_
    have hk : A + ((n + n0 : ℕ) : ℤ) = M + n := by push_cast; omega
    simp only [hg]
    rw [hk, N.shellCoeff_of_le hη Φ hM (by omega), zpow_add₀ hw0, zpow_natCast]
    ring
  have h1 := htail.sum_range_add
  have h2 : HasSum g _ := (N.mellin_hasSum η hηc Φ hA hs).2
  exact h2.unique h1

omit [MeasurableSpace Fˣ] [BorelSpace Fˣ] in
/-- The Mellin threshold: `|c q ^ (-s)| < 1` once `log_q |c| < Re s`. -/
theorem norm_mul_spectralPoint_lt_one (c : ℂ) {s : ℂ} (hs : Real.logb N.q ‖c‖ < s.re) :
    ‖c * spectralPoint N.q s‖ < 1 := by
  have hq1 : (1 : ℝ) < N.q := by exact_mod_cast N.one_lt_q
  have hq0 : (0 : ℝ) < N.q := by linarith
  rw [norm_mul, spectralPoint, Complex.norm_natCast_cpow_of_pos N.q_pos, Complex.neg_re,
    Real.rpow_neg hq0.le]
  have hpos : 0 < (N.q : ℝ) ^ s.re := Real.rpow_pos_of_pos hq0 _
  rw [← div_eq_mul_inv, div_lt_one hpos]
  by_cases hc : c = 0
  · rw [hc, norm_zero]
    exact hpos
  · exact (Real.logb_lt_iff_lt_rpow hq1 (norm_pos_iff.mpr hc)).mp hs

end Mellin

end Normalization

end Langlands.GodementJacquet.LocalTate
