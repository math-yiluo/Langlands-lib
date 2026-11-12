import Langlands.Representation.GodementJacquet.LocalTateLaurent

/-! # The local functional equation for Laurent numerators -/

noncomputable section

namespace Langlands.GodementJacquet.LocalTate

open MeasureTheory HarmonicAnalysis Topology ValuativeRel Conductor RankinSelberg Polynomial
open GeneralLinear.Iwasawa
open scoped ENNReal NNReal

universe uF

namespace Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (N : Normalization F)

section Dual

/-- The residue cardinality as a complex unit. -/
def qUnit : ℂˣ := Units.mk0 (N.q : ℂ) (by exact_mod_cast N.q_pos.ne')

/-- The dual spectral variable `q⁻¹ x⁻¹`. -/
def dualUnit (x : ℂˣ) : ℂˣ := N.qUnit⁻¹ * x⁻¹

theorem coe_dualUnit (x : ℂˣ) : (N.dualUnit x : ℂ) = (N.q : ℂ)⁻¹ * (x : ℂ)⁻¹ := by
  simp [dualUnit, qUnit]

theorem dualUnit_dualUnit (x : ℂˣ) : N.dualUnit (N.dualUnit x) = x := by
  rw [dualUnit, dualUnit, mul_inv_rev, inv_inv, inv_inv, mul_left_comm, inv_mul_cancel, mul_one]

theorem coe_dualUnit_spectralUnit (s : ℂ) :
    (N.dualUnit (spectralUnit N.q_pos s) : ℂ) = spectralPoint N.q (1 - s) := by
  rw [coe_dualUnit, coe_spectralUnit, spectralPoint_sub_one_sub N.q_pos]

theorem coe_dualUnit_zpow (x : ℂˣ) (k : ℤ) :
    (N.dualUnit x : ℂ) ^ k = (N.q : ℂ) ^ (-k) * (x : ℂ) ^ (-k) := by
  rw [coe_dualUnit, mul_zpow, inv_zpow', inv_zpow']

/-- The functional equation between Laurent numerators, with constant `c` and
exponent `a`, in the spectral variable `x = q ^ (-s)`. -/
def DualRelation (c : ℂ) (a : ℕ) (ℓ ℓ' : LaurentCoefficients) : Prop :=
  ∀ x : ℂˣ, laurentEval (N.dualUnit x) ℓ' = c * (x : ℂ) ^ (a : ℤ) * laurentEval x ℓ

end Dual

section Indicators

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem one_notMem_ball_one : (1 : F) ∉ N.ball 1 := by
  rw [N.mem_ball_iff_ord one_ne_zero, (N.ord_eq_zero_iff one_ne_zero).mpr (map_one _)]
  omega

theorem indicator_one_congr {α β : Type*} {s : Set α} {t : Set β} {x : α} {y : β} (h : x ∈ s ↔ y ∈ t) :
    s.indicator (fun _ => (1 : ℂ)) x = t.indicator (fun _ => (1 : ℂ)) y := by
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h.mp hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hy => hx (h.mpr hy))]

/-- A coset of `ϖ ^ n O` through a point of `ϖ ^ n O` is a dilate of `O`. -/
theorem cosetIndicator_eq_dilate_of_mem {x0 : F} {n : ℤ} (hx0 : x0 ∈ N.ball n) :
    N.cosetIndicator x0 n = dilate (N.ϖ ^ (-n)) (N.cosetIndicator 0 0) := by
  apply Subtype.ext
  funext x
  change N.cosetIndicator x0 n x = N.cosetIndicator 0 0 (((N.ϖ ^ (-n) : Fˣ) : F) * x)
  rw [cosetIndicator_apply, cosetIndicator_apply]
  apply indicator_one_congr
  simp only [Set.mem_ofPred_eq, sub_zero]
  have h := N.units_mul_mem_ball_iff (N.ϖ ^ (-n)) (n := n) (x := x)
  rw [Units.val_zpow_eq_zpow_val, N.ord_zpow_ϖ, add_neg_cancel] at h
  rw [Units.val_zpow_eq_zpow_val, h]
  constructor
  · intro hx
    simpa using (N.ball n).add_mem hx hx0
  · intro hx
    exact (N.ball n).sub_mem hx hx0

/-- A coset of `ϖ ^ n O` not containing zero is a dilate of a principal-unit level. -/
theorem cosetIndicator_eq_dilate_of_notMem {x0 : F} {n : ℤ} (hx0 : x0 ∉ N.ball n) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ b : Fˣ, N.cosetIndicator x0 n = dilate b (N.cosetIndicator 1 m) := by
  have hne : x0 ≠ 0 := by
    rintro rfl
    exact hx0 (zero_mem _)
  have hlt : N.ord x0 < n := by
    by_contra h
    exact hx0 ((N.mem_ball_iff_ord hne).mpr (not_lt.mp h))
  refine ⟨(n - N.ord x0).toNat, by omega, (Units.mk0 x0 hne)⁻¹, ?_⟩
  apply Subtype.ext
  funext x
  change N.cosetIndicator x0 n x =
    N.cosetIndicator 1 ((n - N.ord x0).toNat : ℤ) ((((Units.mk0 x0 hne)⁻¹ : Fˣ) : F) * x)
  rw [cosetIndicator_apply, cosetIndicator_apply]
  apply indicator_one_congr
  simp only [Set.mem_ofPred_eq]
  have h := N.units_mul_mem_ball_iff (Units.mk0 x0 hne)⁻¹ (n := n) (x := x - x0)
  have hord : n + N.ord (((Units.mk0 x0 hne)⁻¹ : Fˣ) : F) = ((n - N.ord x0).toNat : ℤ) := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, N.ord_inv hne]
    omega
  have hval : (((Units.mk0 x0 hne)⁻¹ : Fˣ) : F) * (x - x0) =
      (((Units.mk0 x0 hne)⁻¹ : Fˣ) : F) * x - 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, mul_sub, inv_mul_cancel₀ hne]
  rw [hord, hval] at h
  exact h.symm

end Indicators

variable [MeasurableSpace Fˣ] [BorelSpace Fˣ]

section Numerators

theorem laurentEval_shellLaurent (x : ℂˣ) (η : Fˣ →* ℂˣ) (a : ℕ) (Φ : SchwartzBruhat F)
    (A M : ℤ) :
    laurentEval x (N.shellLaurent η a Φ A M) =
      (N.eulerPoly η a).eval (x : ℂ) *
          ∑ n ∈ Finset.range (M - A).toNat,
            (η N.ϖ : ℂ) ^ (A + n) * N.shellCoeff η Φ (A + n) * (x : ℂ) ^ (A + n) +
        Φ 0 * (if a = 0 then 1 else 0) * (η N.ϖ : ℂ) ^ M * (x : ℂ) ^ M := by
  simp only [shellLaurent, map_add, map_mul, map_sum, laurentEval_toLaurent, laurentEval_C,
    laurentEval_T]

theorem HasLaurentMellin.congr {η : Fˣ →* ℂˣ} {P : ℂ[X]} {Φ : SchwartzBruhat F}
    {ℓ ℓ₂ : LaurentCoefficients} (h : N.HasLaurentMellin η P Φ ℓ)
    (he : ∀ x : ℂˣ, laurentEval x ℓ = laurentEval x ℓ₂) : N.HasLaurentMellin η P Φ ℓ₂ := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ, fun s hs => ⟨(hσ s hs).1, (hσ s hs).2.trans (he _)⟩⟩

/-- Laurent data of the indicator of `O`. -/
theorem hasLaurentMellin_integer {η : Fˣ →* ℂˣ} (hηc : Continuous η) {a : ℕ}
    (hη : N.IsUnitConductor η a) :
    N.HasLaurentMellin η (N.eulerPoly η a) (N.cosetIndicator 0 0)
      (LaurentPolynomial.C (if a = 0 then 1 else 0)) := by
  classical
  have hval : ∀ x, N.cosetIndicator 0 0 x = if x ∈ N.ball 0 then 1 else 0 := by
    intro x
    rw [cosetIndicator_apply, Set.indicator_apply]
    simp
  have hA : ∀ x, x ∉ N.ball 0 → N.cosetIndicator 0 0 x = 0 := by
    intro x hx
    rw [hval, ite_eq_right hx]
  have hM : ∀ x ∈ N.ball 0, N.cosetIndicator 0 0 x = N.cosetIndicator 0 0 0 := by
    intro x hx
    rw [hval, hval, ite_eq_left hx, ite_eq_left (zero_mem _)]
  refine (N.hasLaurentMellin_shellLaurent hηc hη _ le_rfl hA hM).congr N fun x => ?_
  rw [laurentEval_shellLaurent, hval, ite_eq_left (zero_mem _)]
  simp

/-- The shell coefficient at order zero of the indicator of a principal-unit level. -/
theorem shellCoeff_unitLevel {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a) {m : ℕ}
    (hm : 1 ≤ m) :
    N.shellCoeff η (N.cosetIndicator 1 m) 0 =
      if a ≤ m then ((localMultiplicativeHaar F (N.unitLevel m : Set Fˣ)).toReal : ℂ)
      else 0 := by
  rw [← N.setIntegral_unitLevel_char hη m, shellCoeff,
    ← Set.inter_eq_right.mpr (N.unitLevel_le_integralUnits m),
    ← setIntegral_indicator (N.isOpen_unitLevel m).measurableSet]
  refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u _ => ?_
  rw [zpow_zero, one_mul, cosetIndicator_apply]
  by_cases hu : u ∈ N.unitLevel m
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem
      (show (u : F) ∈ {x : F | x - 1 ∈ N.ball m} from (N.mem_unitLevel_iff_of_pos hm).mp hu),
      one_mul]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem
      (show (u : F) ∉ {x : F | x - 1 ∈ N.ball m} from
        fun h => hu ((N.mem_unitLevel_iff_of_pos hm).mpr h)), zero_mul]

omit [MeasurableSpace Fˣ] [BorelSpace Fˣ] in
theorem cosetIndicator_one_apply_of_mem_ball_one {m : ℕ} (hm : 1 ≤ m) {x : F}
    (hx : x ∈ N.ball 1) : N.cosetIndicator 1 m x = 0 := by
  rw [cosetIndicator_apply, Set.indicator_of_notMem]
  intro h
  have h' : x - 1 ∈ N.ball 1 := N.ball_antitone (by exact_mod_cast hm) h
  apply N.one_notMem_ball_one
  simpa using (N.ball 1).sub_mem hx h'

/-- Laurent data of the indicator of the principal-unit level `1 + ϖ ^ m O`. -/
theorem hasLaurentMellin_unitLevel {η : Fˣ →* ℂˣ} (hηc : Continuous η) {a : ℕ}
    (hη : N.IsUnitConductor η a) {m : ℕ} (hm : 1 ≤ m) :
    N.HasLaurentMellin η (N.eulerPoly η a) (N.cosetIndicator 1 m)
      (Polynomial.toLaurent (N.eulerPoly η a) * LaurentPolynomial.C
        (if a ≤ m then ((localMultiplicativeHaar F (N.unitLevel m : Set Fˣ)).toReal : ℂ)
          else 0)) := by
  have h0 : N.cosetIndicator 1 m 0 = 0 := N.cosetIndicator_one_apply_of_mem_ball_one hm (zero_mem _)
  have hA : ∀ x, x ∉ N.ball 0 → N.cosetIndicator 1 m x = 0 := by
    intro x hx
    rw [cosetIndicator_apply, Set.indicator_of_notMem]
    intro h
    apply hx
    have h' : x - 1 ∈ N.ball 0 := N.ball_antitone (by positivity) h
    have h1 : (1 : F) ∈ N.ball 0 := by
      rw [mem_ball, map_one, zpow_zero]
    simpa using (N.ball 0).add_mem h' h1
  have hM : ∀ x ∈ N.ball 1, N.cosetIndicator 1 m x = N.cosetIndicator 1 m 0 := by
    intro x hx
    rw [h0, N.cosetIndicator_one_apply_of_mem_ball_one hm hx]
  refine (N.hasLaurentMellin_shellLaurent hηc hη _ zero_le_one hA hM).congr N fun x => ?_
  rw [laurentEval_shellLaurent, h0]
  simp only [sub_zero, Int.toNat_one, Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
    add_zero, zpow_zero, N.shellCoeff_unitLevel hη hm, one_mul, mul_one, zero_mul, map_mul,
    laurentEval_toLaurent, laurentEval_C]

end Numerators

section Gauss

variable {ψ : UnitaryAdditiveCharacter F} (hψ : HasIntegerConductor ψ)
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

include hψ ν in
/-- Of the Gauss integrals at negative orders only the one at `-max a 1` survives. -/
theorem gaussIntegral_eq_zero_of_ne {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a)
    {k : ℤ} (hk0 : k < 0) (hk : k ≠ -((max a 1 : ℕ) : ℤ)) : N.gaussIntegral ψ η k = 0 := by
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · exact N.gaussIntegral_eq_zero_of_lt hψ ν hη hlt
  · apply N.gaussIntegral_eq_zero_of_neg hψ hη hk0
    have : max a 1 = a ∨ max a 1 = 1 := max_choice a 1
    rcases this with h | h
    · rw [h] at hgt
      exact hgt
    · rw [h] at hgt
      omega

omit [MeasurableSpace F] [BorelSpace F] in
open Classical in
/-- Shell coefficients of the Fourier transform of a principal-unit level. -/
theorem shellCoeff_of_fourier_unitLevel (η : Fˣ →* ℂˣ) {m : ℕ} {Ψ : F → ℂ} {C : ℂ}
    (hΨ : ∀ y, Ψ y = ψ.complex y * if y ∈ N.ball (-(m : ℤ)) then C else 0) {k : ℤ}
    (hk : -(m : ℤ) ≤ k) : N.shellCoeff η Ψ k = C * N.gaussIntegral ψ η k := by
  rw [shellCoeff, gaussIntegral, ← integral_const_mul]
  refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
  have hu0 : (u : F) ∈ N.ball 0 := by
    rw [mem_ball, mem_integralUnits_iff.mp hu, zpow_zero]
  have hmem : (N.ϖ : F) ^ k * u ∈ N.ball (-(m : ℤ)) :=
    N.ball_antitone hk (by simpa using N.mul_mem_ball (N.ϖ_zpow_mem_ball k) hu0)
  rw [hΨ, ite_eq_left hmem]
  ring

open Classical in
include hψ ν in
/-- The finite part of the dual shell expansion of a principal-unit level. -/
theorem sum_shellCoeff_fourier_unitLevel {η : Fˣ →* ℂˣ} {a : ℕ} (hη : N.IsUnitConductor η a)
    {m : ℕ} {Ψ : F → ℂ} {C : ℂ}
    (hΨ : ∀ y, Ψ y = ψ.complex y * if y ∈ N.ball (-(m : ℤ)) then C else 0) (y : ℂ) :
    ∑ n ∈ Finset.range m,
        (η N.ϖ : ℂ) ^ (-(m : ℤ) + n) * N.shellCoeff η Ψ (-(m : ℤ) + n) * y ^ (-(m : ℤ) + n) =
      if max a 1 ≤ m then
        (η N.ϖ : ℂ) ^ (-((max a 1 : ℕ) : ℤ)) * (C * N.gaussIntegral ψ η (-((max a 1 : ℕ) : ℤ))) *
          y ^ (-((max a 1 : ℕ) : ℤ))
      else 0 := by
  have hterm : ∀ n ∈ Finset.range m,
      (η N.ϖ : ℂ) ^ (-(m : ℤ) + n) * N.shellCoeff η Ψ (-(m : ℤ) + n) * y ^ (-(m : ℤ) + n) =
        (η N.ϖ : ℂ) ^ (-(m : ℤ) + n) * (C * N.gaussIntegral ψ η (-(m : ℤ) + n)) *
          y ^ (-(m : ℤ) + n) := by
    intro n _
    rw [N.shellCoeff_of_fourier_unitLevel η hΨ (k := -(m : ℤ) + n) (by omega)]
  rw [Finset.sum_congr rfl hterm]
  have hzero : ∀ n ∈ Finset.range m, -(m : ℤ) + n ≠ -((max a 1 : ℕ) : ℤ) →
      (η N.ϖ : ℂ) ^ (-(m : ℤ) + n) * (C * N.gaussIntegral ψ η (-(m : ℤ) + n)) *
        y ^ (-(m : ℤ) + n) = 0 := by
    intro n hn hne
    have hn' : n < m := Finset.mem_range.mp hn
    rw [N.gaussIntegral_eq_zero_of_ne hψ ν hη (by omega) hne]
    ring
  split_ifs with ham
  · have h1 : 1 ≤ max a 1 := le_max_right a 1
    rw [Finset.sum_eq_single (m - max a 1)]
    · have he : -(m : ℤ) + ((m - max a 1 : ℕ) : ℤ) = -((max a 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub ham]
        ring
      rw [he]
    · intro n hn hne
      apply hzero n hn
      intro h
      apply hne
      omega
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · apply Finset.sum_eq_zero
    intro n hn
    apply hzero n hn
    have hn' : n < m := Finset.mem_range.mp hn
    omega

end Gauss

section FunctionalEquation

variable [MeasurableSpace F] [BorelSpace F]
variable (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F) (χ : Fˣ →* ℂˣ) (a : ℕ)

/-- The Laurent form of the local functional equation for one test function:
the Fourier transform is again a test function, and the two Laurent numerators
satisfy the dual relation with constant `c`. -/
def FEData (c : ℂ) (Φ : SchwartzBruhat F) : Prop :=
  ∃ Ψ : SchwartzBruhat F, (∀ y, Ψ y = fourierIntegral ψ ν Φ y) ∧
    ∃ ℓ ℓ' : LaurentCoefficients, N.HasLaurentMellin χ (N.eulerPoly χ a) Φ ℓ ∧
      N.HasLaurentMellin χ⁻¹ (N.eulerPoly χ⁻¹ a) Ψ ℓ' ∧ N.DualRelation c a ℓ ℓ'

/-- The constant of the functional equation. -/
def feConstant : ℂ :=
  if a = 0 then ((ν.measure (N.ball 0)).toReal : ℂ)
  else ((ν.measure (unitShell F)).toReal : ℂ) * (N.q : ℂ) ^ a * (χ N.ϖ : ℂ) ^ a *
    N.gaussIntegral ψ χ⁻¹ (-(a : ℤ))

variable {ψ ν χ a}

omit [BorelSpace F] in
theorem feData_zero (c : ℂ) : N.FEData ψ ν χ a c 0 := by
  refine ⟨0, fun y => ?_, 0, 0, N.hasLaurentMellin_zero _ _, N.hasLaurentMellin_zero _ _,
    fun x => by simp⟩
  simp [fourierIntegral]

theorem feData_add {c : ℂ} {Φ₁ Φ₂ : SchwartzBruhat F} (h₁ : N.FEData ψ ν χ a c Φ₁)
    (h₂ : N.FEData ψ ν χ a c Φ₂) : N.FEData ψ ν χ a c (Φ₁ + Φ₂) := by
  obtain ⟨Ψ₁, hΨ₁, ℓ₁, ℓ₁', h₁, h₁', hd₁⟩ := h₁
  obtain ⟨Ψ₂, hΨ₂, ℓ₂, ℓ₂', h₂, h₂', hd₂⟩ := h₂
  refine ⟨Ψ₁ + Ψ₂, fun y => ?_, ℓ₁ + ℓ₂, ℓ₁' + ℓ₂', N.hasLaurentMellin_add h₁ h₂,
    N.hasLaurentMellin_add h₁' h₂', fun x => ?_⟩
  · have h := congrFun (map_add (fourierTransform ψ ν) Φ₁ Φ₂) y
    change fourierIntegral ψ ν (Φ₁ + Φ₂) y =
      fourierIntegral ψ ν Φ₁ y + fourierIntegral ψ ν Φ₂ y at h
    rw [Submodule.coe_add, Submodule.coe_add, h, ← hΨ₁, ← hΨ₂]
    rfl
  · rw [map_add, map_add, hd₁, hd₂]
    ring

theorem feData_smul {c : ℂ} (k : ℂ) {Φ : SchwartzBruhat F} (h : N.FEData ψ ν χ a c Φ) :
    N.FEData ψ ν χ a c (k • Φ) := by
  obtain ⟨Ψ, hΨ, ℓ, ℓ', h, h', hd⟩ := h
  refine ⟨k • Ψ, fun y => ?_, k • ℓ, k • ℓ', N.hasLaurentMellin_smul h k,
    N.hasLaurentMellin_smul h' k, fun x => ?_⟩
  · have h := congrFun (map_smul (fourierTransform ψ ν) k Φ) y
    change fourierIntegral ψ ν (k • Φ) y = k * fourierIntegral ψ ν Φ y at h
    rw [Submodule.coe_smul, Submodule.coe_smul, h, ← hΨ]
    rfl
  · rw [laurentEval_smul, laurentEval_smul, hd]
    ring

theorem feData_dilate {c : ℂ} (b : Fˣ) {Φ : SchwartzBruhat F} (h : N.FEData ψ ν χ a c Φ) :
    N.FEData ψ ν χ a c (dilate b Φ) := by
  obtain ⟨Ψ, hΨ, ℓ, ℓ', h, h', hd⟩ := h
  refine ⟨((N.abv (b : F))⁻¹ : ℂ) • dilate b⁻¹ Ψ, fun y => ?_, _, _,
    N.hasLaurentMellin_dilate h b, N.hasLaurentMellin_smul (N.hasLaurentMellin_dilate h' b⁻¹) _,
    fun x => ?_⟩
  · rw [N.fourierIntegral_dilate ψ ν b Φ y, ← hΨ]
    rfl
  · set k := N.ord (b : F) with hk
    have hq0 : (N.q : ℂ) ≠ 0 := by exact_mod_cast N.q_pos.ne'
    have hx0 : (x : ℂ) ≠ 0 := x.ne_zero
    have hord : -N.ord (((b⁻¹ : Fˣ) : F)) = k := by
      rw [Units.val_inv_eq_inv_val, N.ord_inv b.ne_zero, neg_neg]
    have hchi : (((χ⁻¹ (b⁻¹)) : ℂˣ) : ℂ)⁻¹ = (χ b : ℂ)⁻¹ := by
      simp
    have habs : ((N.abv (b : F) : ℂ))⁻¹ = (N.q : ℂ) ^ k := by
      rw [N.abv_eq b.ne_zero, Complex.ofReal_zpow, Complex.ofReal_natCast, zpow_neg, inv_inv]
    rw [laurentEval_smul, map_mul, map_mul, laurentEval_C, laurentEval_T, hd, map_mul, map_mul,
      laurentEval_C, laurentEval_T, hord, hchi, habs, N.coe_dualUnit_zpow, zpow_neg, zpow_neg]
    have e : (N.q : ℂ) ^ k * ((N.q : ℂ) ^ k)⁻¹ = 1 := mul_inv_cancel₀ (zpow_ne_zero _ hq0)
    linear_combination
      (c * (x : ℂ) ^ (a : ℤ) * (χ b : ℂ)⁻¹ * ((x : ℂ) ^ k)⁻¹ * laurentEval x ℓ) * e

variable (hψ : HasIntegerConductor ψ)
include hψ

/-- The functional equation for the indicator of `O`. -/
theorem feData_integer (hχc : Continuous χ) (hχ : N.IsUnitConductor χ a) :
    N.FEData ψ ν χ a (N.feConstant ψ ν χ a) (N.cosetIndicator 0 0) := by
  classical
  set c0 : ℂ := ((ν.measure (N.ball 0)).toReal : ℂ) with hc0
  have hχc' : Continuous (χ⁻¹ : Fˣ →* ℂˣ) := continuous_inv.comp hχc
  refine ⟨c0 • N.cosetIndicator 0 0, fun y => ?_, _, _, N.hasLaurentMellin_integer hχc hχ,
    N.hasLaurentMellin_smul (N.hasLaurentMellin_integer hχc' hχ.inv) c0, fun x => ?_⟩
  · rw [N.fourierIntegral_cosetIndicator hψ ν 0 0 y, zero_mul, AddChar.map_zero_eq_one, one_mul,
      neg_zero]
    change c0 * N.cosetIndicator 0 0 y = _
    rw [cosetIndicator_apply, Set.indicator_apply]
    simp only [Set.mem_ofPred_eq, sub_zero]
    split_ifs <;> simp [hc0]
  · rw [laurentEval_smul, laurentEval_C, laurentEval_C, feConstant]
    split_ifs with ha
    · subst ha
      simp [hc0]
    · simp

/-- The functional equation for the indicator of a principal-unit level. -/
theorem feData_unitLevel [T2Space F] [TotallyDisconnectedSpace F] (hν : IsSelfDual ψ ν)
    (hχc : Continuous χ) (hχ : N.IsUnitConductor χ a) {m : ℕ} (hm : 1 ≤ m) :
    N.FEData ψ ν χ a (N.feConstant ψ ν χ a) (N.cosetIndicator 1 m) := by
  classical
  have hχc' : Continuous (χ⁻¹ : Fˣ →* ℂˣ) := continuous_inv.comp hχc
  obtain ⟨Ψ, hΨ⟩ := exists_scalar_fourier_witness ψ ν hν (N.cosetIndicator 1 m)
  have hΨv : ∀ y, Ψ y = ψ.complex y *
      if y ∈ N.ball (-(m : ℤ)) then ((ν.measure (N.ball m)).toReal : ℂ) else 0 := by
    intro y
    rw [(hΨ y).2, N.fourierIntegral_cosetIndicator hψ ν 1 m y, one_mul]
  have hΨ0 : Ψ 0 = ((ν.measure (N.ball m)).toReal : ℂ) := by
    rw [hΨv, ite_eq_left (zero_mem _), AddChar.map_zero_eq_one, one_mul]
  have hA : ∀ y, y ∉ N.ball (-(m : ℤ)) → Ψ y = 0 := by
    intro y hy
    rw [hΨv, ite_eq_right hy, mul_zero]
  have hM : ∀ y ∈ N.ball 0, Ψ y = Ψ 0 := by
    intro y hy
    rw [hΨ0, hΨv, ite_eq_left (N.ball_antitone (by omega) hy),
      N.char_eq_one_of_mem_ball_zero hψ hy, one_mul]
  refine ⟨Ψ, fun y => (hΨ y).2, _, _, N.hasLaurentMellin_unitLevel hχc hχ hm,
    N.hasLaurentMellin_shellLaurent hχc' hχ.inv Ψ (by omega) hA hM, fun x => ?_⟩
  have hrange : ((0 : ℤ) - -(m : ℤ)).toNat = m := by omega
  rw [laurentEval_shellLaurent, hrange,
    N.sum_shellCoeff_fourier_unitLevel hψ ν.measure hχ.inv hΨv, hΨ0, map_mul,
    laurentEval_toLaurent, laurentEval_C, N.measure_unitLevel ν.measure hm, feConstant]
  have hU0 : ((ν.measure (unitShell F)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (N.measure_unitShell_toReal_pos ν.measure).ne'
  have hq0 : (N.q : ℂ) ≠ 0 := by exact_mod_cast N.q_pos.ne'
  have hinv : ((χ⁻¹ N.ϖ : ℂˣ) : ℂ) = (χ N.ϖ : ℂ)⁻¹ := by simp
  have e4 : ((ν.measure (unitShell F)).toReal : ℂ) *
      ((ν.measure (unitShell F)).toReal : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hU0
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- unramified case
    subst ha
    have hG := N.gaussIntegral_neg_one hψ ν.measure (η := χ⁻¹) hχ.inv
    have hO : ((ν.measure (N.ball 0)).toReal : ℂ) =
        ((ν.measure (unitShell F)).toReal : ℂ) + ((ν.measure (N.ball 1)).toReal : ℂ) := by
      rw [N.measure_unitShell ν.measure]
      push_cast
      ring
    have hqB : (N.q : ℝ) * (ν.measure (N.ball 1)).toReal = (ν.measure (N.ball 0)).toReal := by
      rw [N.measure_ball ν.measure 1, zpow_neg, zpow_one, ← mul_assoc,
        mul_inv_cancel₀ (by exact_mod_cast N.q_pos.ne'), one_mul]
    have hb1 : (N.q : ℂ) * ((ν.measure (N.ball 1)).toReal : ℂ) =
        ((ν.measure (unitShell F)).toReal : ℂ) + ((ν.measure (N.ball 1)).toReal : ℂ) := by
      rw [← hO]
      exact_mod_cast hqB
    have e1 : (χ N.ϖ : ℂ) * (χ N.ϖ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (χ N.ϖ).ne_zero
    have e2 : (N.q : ℂ) * (N.q : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hq0
    have e3 : (x : ℂ) * (x : ℂ)⁻¹ = 1 := mul_inv_cancel₀ x.ne_zero
    simp only [eulerPoly, max_eq_right (Nat.zero_le 1), hm, Nat.zero_le, ↓reduceIte,
      Nat.cast_one, Nat.cast_zero, zpow_zero, zpow_neg, zpow_one, mul_one, eval_sub, eval_one, eval_mul, eval_C, eval_X, hG, hinv, N.coe_dualUnit, mul_inv, inv_inv]
    rw [hO]
    push_cast
    set w : ℂ := (χ N.ϖ : ℂ)
    set Mm : ℂ := ((ν.measure (N.ball m)).toReal : ℂ)
    set B : ℂ := ((ν.measure (N.ball 1)).toReal : ℂ)
    set U : ℂ := ((ν.measure (unitShell F)).toReal : ℂ)
    set q : ℂ := (N.q : ℂ)
    linear_combination (Mm * B * U⁻¹ * q * q⁻¹ * x * x⁻¹) * e1 + (Mm * B * U⁻¹ * x * x⁻¹) * e2 +
      (Mm * B * U⁻¹) * e3 - Mm * e4 - (w * x * Mm * U⁻¹) * hb1
  · -- ramified case
    have ha0 : a ≠ 0 := by omega
    have hmax : max a 1 = a := max_eq_left (by omega)
    simp only [hmax, eulerPoly, ha0, ↓reduceIte, eval_one, one_mul, hinv,
      N.coe_dualUnit, zpow_neg, zpow_natCast, inv_pow, mul_pow, mul_inv, inv_inv, mul_zero,
      zero_mul, add_zero]
    split_ifs with ham
    · push_cast
      linear_combination
        (-((χ N.ϖ : ℂ) ^ a * ((ν.measure (N.ball m)).toReal : ℂ) *
          N.gaussIntegral ψ χ⁻¹ (-(a : ℤ)) * (N.q : ℂ) ^ a * (x : ℂ) ^ a)) * e4
    · simp

end FunctionalEquation

end Normalization

end Langlands.GodementJacquet.LocalTate
