import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof

/-!
# Growth bounds for the Section 4.7 lower quotient

The standard-character test coefficient has a uniform geometric growth base.
Block section bounds follow from finite compact images and the exact opposite twist.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.RankinSelberg.TwoBlockLowerFixedSlice

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockJacquet TwoBlockDeformation
  TwoBlockConvergence

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

/-- The standard-character counterpart of the inverse-functional growth estimate.
The base depends on the representation and functional, before the vector. -/
theorem exists_standard_functional_growth (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsOfWhittakerType n (standardCharacter ψ n) ρ) (ℓ : glFunctionals ψ n ρ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ v : V, ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (n + 1) F.Carrier),
      IsEntryBounded (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) e g →
        ‖ℓ.val (ρ g v)‖ ≤ C * B ^ e := by
  set T := F.canonicalTopologicalData
  have hϖ := uniformizerUnit_isUniformizingElement F
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F.Carrier, ψ x₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact ψ.nontrivial (AddChar.ext _ _ hcon)
  have hχ₀ : ψ.complex x₀ ≠ 1 := by
    rw [ne_eq, UnitaryAdditiveCharacter.complex_apply, Circle.coe_eq_one]
    exact hx₀
  obtain ⟨c₀, hc₀⟩ := exists_pow_mul_mem_integer hϖ x₀
  obtain ⟨n₀, hn₀⟩ := T.exists_additiveTrivialAt ψ
  refine exists_growth ρ hρ.1 hρ.2.1 ℓ.val ψ.complex
    (fun x hx v => ℓ.property ⟨x, hx⟩ v)
    (fun z => ψ.norm_complex z) hϖ hχ₀ hc₀ (a₀ := (-n₀).toNat)
    fun z hz => ?_
  have hz1 : ψ z = 1 := by
    refine hn₀ z ?_
    rw [T.mem_additiveLattice_iff_div_mem_integers,
      ← LocalFactor.PadicAbelian.uniformizerUnit_coe T]
    have hpos := Iwasawa.valuation_pos (ValuativeRel.valuation F.Carrier)
      (LocalFactor.PadicAbelian.uniformizerUnit T)
    have hle := valuation_le_of_mem_levelSet hϖ hz
    change ValuativeRel.valuation F.Carrier
      (z / (LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) ^ (-n₀)) ≤ 1
    rw [map_div₀, map_zpow₀, zpow_neg, div_inv_eq_mul]
    have hn : 0 ≤ ((-n₀).toNat : ℤ) + n₀ := by
      have := Int.self_le_toNat (-n₀)
      omega
    calc
      ValuativeRel.valuation F.Carrier z *
          ValuativeRel.valuation F.Carrier
            (LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) ^ n₀ ≤
          ValuativeRel.valuation F.Carrier
              (LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) ^ (-n₀).toNat *
            ValuativeRel.valuation F.Carrier
              (LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) ^ n₀ :=
        by gcongr
      _ = ValuativeRel.valuation F.Carrier
            (LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) ^
              (((-n₀).toNat : ℤ) + n₀) := by
        rw [zpow_add₀ hpos.ne', zpow_natCast]
      _ ≤ 1 := (zpow_le_one_iff_right_of_lt_one₀ hpos hϖ.1).mpr hn
  rw [UnitaryAdditiveCharacter.complex_apply, hz1, Circle.coe_one]


/-- Every actual coefficient-image vector inherits the same growth base. -/
theorem exists_coefficient_growth (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) (ell : glFunctionals ψ n π) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ W : (coefficientModel π ell).toSubmodule,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : ℕ) (g : GeneralLinear (n + 1) F.Carrier),
        IsEntryBounded (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) e g →
          ‖W.val.val g‖ ≤ C * B ^ e := by
  obtain ⟨B, hB, hgrowth⟩ := exists_standard_functional_growth F ψ π hπ ell
  refine ⟨B, hB, fun W => ?_⟩
  obtain ⟨v, hv⟩ := modelMap_surjective π ell W
  obtain ⟨C, hC⟩ := hgrowth v
  refine ⟨max C 0, le_max_right _ _, fun e g hg => ?_⟩
  have hW : W.val.val g = ell.val (π g v) := by
    rw [← hv]
    rfl
  rw [hW]
  exact (hC e g hg).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans hB) e))

/-- A diagonal uniformizer matrix is entry-bounded by any common bound for
its positive and negative exponents. -/
theorem isEntryBounded_torus {n : ℕ} {ϖ : F.Carrierˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    (lam : Fin n → ℤ) (e : ℕ) (he : ∀ i, -(e : ℤ) ≤ lam i ∧ lam i ≤ e) :
    IsEntryBounded ϖ e (Iwasawa.torus ϖ lam) := by
  have hpow (z : ℤ) :
      (ϖ : F.Carrier) ^ e * ((ϖ ^ z : F.Carrierˣ) : F.Carrier) =
        ((ϖ ^ ((e : ℤ) + z) : F.Carrierˣ) : F.Carrier) := by
    rw [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  intro i j
  by_cases hij : i = j
  · subst j
    constructor
    · change (ϖ : F.Carrier) ^ e *
        (Iwasawa.torus ϖ lam).val i i ∈ (ValuativeRel.valuation F.Carrier).integer
      rw [Iwasawa.torus_val, Matrix.diagonal_apply_eq, hpow]
      exact zpow_mem_integer_of_nonneg hϖ.1.le (by have := (he i).1; omega)
    · change (ϖ : F.Carrier) ^ e *
        (Iwasawa.torus ϖ lam)⁻¹.val i i ∈ (ValuativeRel.valuation F.Carrier).integer
      rw [Iwasawa.torus_inv_val, Matrix.diagonal_apply_eq, ← zpow_neg, hpow]
      exact zpow_mem_integer_of_nonneg hϖ.1.le (by have := (he i).2; omega)
  · constructor
    · change (ϖ : F.Carrier) ^ e *
        (Iwasawa.torus ϖ lam).val i j ∈ (ValuativeRel.valuation F.Carrier).integer
      rw [Iwasawa.torus_val, Matrix.diagonal_apply_ne _ hij, mul_zero]
      exact zero_mem _
    · change (ϖ : F.Carrier) ^ e *
        (Iwasawa.torus ϖ lam)⁻¹.val i j ∈ (ValuativeRel.valuation F.Carrier).integer
      rw [Iwasawa.torus_inv_val, Matrix.diagonal_apply_ne _ hij, mul_zero]
      exact zero_mem _

/-- Uniform growth of actual test coefficients on diagonal/compact coordinates,
including any fixed left translate such as the block rotation. -/
theorem exists_coefficient_torus_growth (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) (ell : glFunctionals ψ n π) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ W : (coefficientModel π ell).toSubmodule,
      ∀ c : GeneralLinear (n + 1) F.Carrier, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (lam : Fin (n + 1) → ℤ) (e : ℕ),
        (∀ i, -(e : ℤ) ≤ lam i ∧ lam i ≤ e) →
        ∀ k ∈ integralOpen F n,
          ‖W.val.val (c * Iwasawa.torus
            (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * k)‖ ≤
              C * B ^ e := by
  obtain ⟨B, hB, hgrowth⟩ := exists_coefficient_growth F ψ π hπ ell
  refine ⟨B, hB, fun W c => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hgrowth W
  have hϖ := uniformizerUnit_isUniformizingElement F
  obtain ⟨ec, hec⟩ := exists_isEntryBounded hϖ c
  refine ⟨C * B ^ ec, mul_nonneg hC0 (pow_nonneg (zero_le_one.trans hB) _),
    fun lam e he k hk => ?_⟩
  have hk' := (mem_integralOpen F k).1 hk
  have hkbounded : IsEntryBounded
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) 0 k := by
    intro i j
    simpa only [pow_zero, one_mul] using And.intro (hk'.1 i j) (hk'.2 i j)
  have hbounded := (hec.mul (isEntryBounded_torus F hϖ lam e he)).mul hkbounded
  rw [add_zero] at hbounded
  calc
    _ ≤ C * B ^ (ec + e) := hC _ _ hbounded
    _ = _ := by rw [pow_add]; ring

/-- The integral `l¹` size of a diagonal exponent vector. -/
def torusSize {n : ℕ} (lam : Fin n → ℤ) : ℕ := ∑ i, (lam i).natAbs

theorem torusSize_bounds {n : ℕ} (lam : Fin n → ℤ) (i : Fin n) :
    -(torusSize lam : ℤ) ≤ lam i ∧ lam i ≤ torusSize lam := by
  have hsum : (lam i).natAbs ≤ torusSize lam :=
    Finset.single_le_sum (f := fun j => (lam j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hcast : ((lam i).natAbs : ℤ) ≤ torusSize lam := by exact_mod_cast hsum
  have hlo := neg_abs_le (lam i)
  have hhi := le_abs_self (lam i)
  rw [← Int.natCast_natAbs] at hlo hhi
  omega

/-- The same coefficient bound with the canonical integral `l¹` size. -/
theorem exists_coefficient_torusSize_growth (ψ : UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) (ell : glFunctionals ψ n π) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ W : (coefficientModel π ell).toSubmodule,
      ∀ c : GeneralLinear (n + 1) F.Carrier, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (lam : Fin (n + 1) → ℤ) (k : GeneralLinear (n + 1) F.Carrier),
        k ∈ integralOpen F n →
          ‖W.val.val (c * Iwasawa.torus
            (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * k)‖ ≤
              C * B ^ torusSize lam := by
  obtain ⟨B, hB, hgrowth⟩ := exists_coefficient_torus_growth F ψ π hπ ell
  refine ⟨B, hB, fun W c => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hgrowth W c
  exact ⟨C, hC0, fun lam k hk => hC lam (torusSize lam) (torusSize_bounds lam) k hk⟩

section Sections

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Uniform block-section growth, with the inverse upper half modulus and both
opposite twists displayed exactly. The growth base precedes the twist and section. -/
theorem exists_section_growth (ψ : UnitaryAdditiveCharacter F.Carrier)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (u : ℝ)
      (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ integralOpen F t, ∀ (e : ℕ)
        (b : (succBlockShape m h).Levi F.Carrier),
        (∀ i, IsEntryBounded
          (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) e (b i)) →
        ‖scalarSection (fun i => (ell i).val) f
          ((succBlockShape m h).leviEmbedding F.Carrier b * k) 1‖ ≤
          C * B ^ e *
            ‖((F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹‖ *
            (((F.canonicalTopologicalData.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) ^ (-u) *
              ((F.canonicalTopologicalData.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) ^ u) := by
  classical
  choose B hB hgrowth using fun i => exists_functional_growth F ψ (τ i) (hτ i) (ell i)
  refine ⟨∏ i, B i, ?_, fun u f => ?_⟩
  · rw [Fin.prod_univ_two]
    exact one_le_mul_of_one_le_of_one_le (hB 0) (hB 1)
  obtain ⟨C, hC0, hC⟩ := exists_integral_growth F h τ
    (twoBlockOppositeTwistBlocks F m τ u) (fun i => (ell i).val)
    (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
    B (fun i => zero_le_one.trans (hB i)) hgrowth f
  refine ⟨C, hC0, fun k hk e b hb => ?_⟩
  have hcov := scalarSection_covariant (fun i => (ell i).val) f
    ((succBlockShape m h).oppositeLeviInParabolic F.Carrier b)
    ((succBlockShape m h).oppositeLeviProjection_section F.Carrier b) k 1
  rw [GeneralLinear.BlockShape.oppositeLeviInParabolic_val, one_mul] at hcov
  have hp0 : 0 < ((F.canonicalTopologicalData.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hp1 : 0 < ((F.canonicalTopologicalData.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  rw [hcov, scalarSection_def,
    tensorContraction_blockTensor_twist F h τ u (fun i => (ell i).val),
    norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hp0,
    Complex.norm_cpow_eq_rpow_re_of_pos hp1, Complex.neg_re, Complex.ofReal_re]
  have hnonneg : 0 ≤
      ‖((F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹‖ *
        (((F.canonicalTopologicalData.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) ^ (-u) *
          ((F.canonicalTopologicalData.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) ^ u) := by
    positivity
  calc
    _ ≤ ‖((F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹‖ *
        (((F.canonicalTopologicalData.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) ^ (-u) *
          ((F.canonicalTopologicalData.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) ^ u) *
        (C * (∏ i, B i) ^ e) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hC k hk e b hb) hnonneg
    _ = _ := by ring

end Sections

end Langlands.RankinSelberg.TwoBlockLowerFixedSlice
