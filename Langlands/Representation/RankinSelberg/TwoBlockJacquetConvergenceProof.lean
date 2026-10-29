import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.FunctionalGrowth
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa
import Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Ordinary absolute convergence of the two-block Jacquet integral

Proof of `Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg.TwoBlockConvergence

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockJacquet TwoBlockDeformation

universe uF uW

section Character

variable {k : Type*} [Field k] [ValuativeRel k]

/-- Elements of `𝔪^a` have valuation at most `v(ϖ)^a`. -/
theorem valuation_le_of_mem_levelSet {ϖ : kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation k) ϖ) {a : ℕ} {z : k}
    (hz : z ∈ UnequalRankMirabolicUnitTest.levelSet k a) :
    ValuativeRel.valuation k z ≤ ValuativeRel.valuation k (ϖ : k) ^ a := by
  have hpos := Iwasawa.valuation_pos (ValuativeRel.valuation k) ϖ
  have hmax : ∀ w ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation k).integer,
      ValuativeRel.valuation k (w : k) ≤ ValuativeRel.valuation k (ϖ : k) := by
    intro w hw
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (ValuativeRel.valuation k)).isUnit_iff_valuation_eq_one] at hw
    have hw1 : ValuativeRel.valuation k (w : k) < 1 := lt_of_le_of_ne w.property hw
    by_cases hw0 : (w : k) = 0
    · rw [hw0, map_zero]
      exact zero_le
    obtain ⟨n, hn⟩ := hϖ.2 _ hw0
    rw [hn] at hw1 ⊢
    have hn1 : 0 < n := (zpow_lt_one_iff_right_of_lt_one₀ hpos hϖ.1).mp hw1
    calc
      ValuativeRel.valuation k (ϖ : k) ^ n ≤ ValuativeRel.valuation k (ϖ : k) ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ hpos hϖ.1.le (by omega)
      _ = ValuativeRel.valuation k (ϖ : k) := zpow_one _
  obtain ⟨y, hy, rfl⟩ := hz
  induction a generalizing y with
  | zero =>
    rw [pow_zero]
    exact y.property
  | succ a ih =>
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun x hx w hw => ?_) (fun x w hx hw => ?_)
    · rw [Subring.coe_mul, map_mul, pow_succ]
      exact mul_le_mul' (ih x hx) (hmax w hw)
    · rw [Subring.coe_add]
      exact (Valuation.map_add _ _ _).trans (max_le hx hw)

end Character

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance proofFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance proofFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance proofFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance proofFieldMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance proofFieldBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

section Functional

/-- The canonical uniformizer is a uniformizing element of the canonical valuation. -/
theorem uniformizerUnit_isUniformizingElement :
    Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier)
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hex : e (ValuativeRel.valuation F.Carrier
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData : F.Carrier)) =
        WithZero.exp (-1) := by
    have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_value F.canonicalTopologicalData 1
    rw [zpow_one] at h
    exact h
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← e.strictMono.lt_iff_lt, hex, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · have hy0 : e (ValuativeRel.valuation F.Carrier y) ≠ 0 := by
      simpa using hy
    refine ⟨-WithZero.log (e (ValuativeRel.valuation F.Carrier y)), ?_⟩
    have key : e (ValuativeRel.valuation F.Carrier y) = e (ValuativeRel.valuation F.Carrier
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData : F.Carrier) ^
          (-WithZero.log (e (ValuativeRel.valuation F.Carrier y)))) := by
      rw [map_zpow₀, hex, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
        WithZero.exp_log hy0]
    exact e.injective key

/-- **Growth of one inverse-character functional.** For a representation of Whittaker type
and a functional equivariant for the inverse standard character, there is one base
`B ≥ 1` such that every vector `v` has a constant `C` with `|ℓ(ρ(g) v)| ≤ C B^e` whenever
`g` is bounded by `e` for the canonical uniformizer. -/
theorem exists_functional_growth (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsOfWhittakerType n (standardCharacter ψ n) ρ) (ℓ : glInverseFunctionals ψ n ρ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ v : V, ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (n + 1) F.Carrier),
      IsEntryBounded (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) e g →
        ‖ℓ.val (ρ g v)‖ ≤ C * B ^ e := by
  set T := F.canonicalTopologicalData
  have hϖ := uniformizerUnit_isUniformizingElement F
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F.Carrier, ψ x₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact ψ.nontrivial (AddChar.ext _ _ hcon)
  have hχ₀ : (ψ.complex x₀)⁻¹ ≠ 1 := by
    rw [ne_eq, inv_eq_one, UnitaryAdditiveCharacter.complex_apply, Circle.coe_eq_one]
    exact hx₀
  obtain ⟨c₀, hc₀⟩ := exists_pow_mul_mem_integer hϖ x₀
  obtain ⟨n₀, hn₀⟩ := T.exists_additiveTrivialAt ψ
  refine exists_growth ρ hρ.1 hρ.2.1 ℓ.val (fun z => (ψ.complex z)⁻¹)
    (fun x hx v => ℓ.property ⟨x, hx⟩ v)
    (fun z => by rw [norm_inv, ψ.norm_complex, inv_one]) hϖ hχ₀ hc₀ (a₀ := (-n₀).toNat)
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
  change (ψ.complex z)⁻¹ = 1
  rw [UnitaryAdditiveCharacter.complex_apply, hz1, Circle.coe_one, inv_one]

end Functional

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

section Tensor

/-- **Growth of block-tensor contractions.** If every block functional grows at most like
`B_i^e` on elements bounded by `e`, then every tensor `w` has a constant `C` with
`|(ℓ_0 ⊗ ℓ_1)((τ_0 ⊗ τ_1)(b) w)| ≤ C (B_0 B_1)^e` whenever both blocks of `b` are bounded
by `e`. -/
theorem exists_blockTensor_growth
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, W i →ₗ[ℂ] ℂ) (ϖ : F.Carrierˣ) (B : Fin 2 → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hgrowth : ∀ i (v : W i), ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (m i + 1) F.Carrier),
      IsEntryBounded ϖ e g → ‖ell i (τ i g v)‖ ≤ C * B i ^ e)
    (w : PiTensorProduct ℂ W) :
    ∃ C : ℝ, ∀ (e : ℕ) (b : (succBlockShape m h).Levi F.Carrier),
      (∀ i, IsEntryBounded ϖ e (b i)) →
      ‖tensorContraction ell ((succBlockShape m h).blockTensor τ b w)‖ ≤
        C * (∏ i, B i) ^ e := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    choose C hC using fun i => hgrowth i (v i)
    refine ⟨‖r‖ * ∏ i, max (C i) 0, fun e b hb => ?_⟩
    rw [map_smul, map_smul, BlockShape.blockTensor_tprod, tensorContraction_tprod, norm_smul,
      norm_prod, mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg r)
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    exact (hC i e (b i) (hb i)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hB i) e))
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨C₁, hC₁⟩ := h₁
    obtain ⟨C₂, hC₂⟩ := h₂
    refine ⟨C₁ + C₂, fun e b hb => ?_⟩
    rw [map_add, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC₁ e b hb) (hC₂ e b hb))

/-- The block tensor of the opposite twists is the scalar `|det b_0|^(-u) |det b_1|^u`
times the untwisted block tensor, after contraction. -/
theorem tensorContraction_blockTensor_twist
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℝ)
    (ell : ∀ i, W i →ₗ[ℂ] ℂ) (b : (succBlockShape m h).Levi F.Carrier)
    (w : PiTensorProduct ℂ W) :
    tensorContraction ell
        ((succBlockShape m h).blockTensor (twoBlockOppositeTwistBlocks F m τ u) b w) =
      ((((F.canonicalTopologicalData.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) : ℂ) ^
          (-(u : ℂ)) *
        (((F.canonicalTopologicalData.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) : ℂ) ^
          (u : ℂ)) *
        tensorContraction ell ((succBlockShape m h).blockTensor τ b w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, map_smul, map_smul, map_smul, BlockShape.blockTensor_tprod,
      BlockShape.blockTensor_tprod, tensorContraction_tprod, tensorContraction_tprod,
      Fin.prod_univ_two, Fin.prod_univ_two, twoBlockOppositeTwistBlocks_apply,
      twoBlockOppositeTwistBlocks_apply]
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, Fin.isValue, one_ne_zero,
      ite_true, ite_false]
    ring
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, map_add, h₁, h₂, mul_add]

end Tensor

section Sections

/-- A section takes finitely many values on the compact subgroup `K₀ = GL_(t+1)(O)`. -/
theorem finite_image_sectionEval_integralOpen
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (f : Sections F h σ) :
    (sectionEval F h σ f '' (integralOpen F t : Set (GeneralLinear (t + 1) F.Carrier))).Finite := by
  have hK := isCompact_integralOpen F t
  rw [isCompact_iff_compactSpace] at hK
  have hloc : IsLocallyConstant
      (fun k : (integralOpen F t : Set (GeneralLinear (t + 1) F.Carrier)) =>
        sectionEval F h σ f k) :=
    (Induction.eval_isLocallyConstant _ _ f).comp_continuous continuous_subtype_val
  rw [Set.image_eq_range]
  exact hloc.range_finite

/-- **Uniform growth on `K₀`.** The block-tensor growth of `exists_blockTensor_growth`
holds with one constant for all the values of a section on `K₀`. -/
theorem exists_integral_growth
    (τ σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (ell : ∀ i, W i →ₗ[ℂ] ℂ) (ϖ : F.Carrierˣ) (B : Fin 2 → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hgrowth : ∀ i (v : W i), ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (m i + 1) F.Carrier),
      IsEntryBounded ϖ e g → ‖ell i (τ i g v)‖ ≤ C * B i ^ e)
    (f : Sections F h σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ integralOpen F t, ∀ (e : ℕ) (b : (succBlockShape m h).Levi F.Carrier),
      (∀ i, IsEntryBounded ϖ e (b i)) →
        ‖tensorContraction ell ((succBlockShape m h).blockTensor τ b (sectionEval F h σ f k))‖ ≤
          C * (∏ i, B i) ^ e := by
  classical
  have hfin := finite_image_sectionEval_integralOpen F h σ f
  choose Cw hCw using fun w => exists_blockTensor_growth F h τ ell ϖ B hB hgrowth w
  refine ⟨∑ w ∈ hfin.toFinset, max (Cw w) 0,
    Finset.sum_nonneg fun _ _ => le_max_right _ _, fun k hk e b hb => ?_⟩
  have hw : sectionEval F h σ f k ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨k, hk, rfl⟩
  refine (hCw _ e b hb).trans
    (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Finset.prod_nonneg fun i _ => hB i) e))
  exact (le_max_left _ _).trans
    (Finset.single_le_sum (f := fun w => max (Cw w) 0) (fun _ _ => le_max_right _ _) hw)

end Sections

section Bounds

/-- If `|det b_0| = q^d` and `|det b_1| = q^(-d)`, the inverse half modulus of the upper
block parabolic at `b` has norm at most one. -/
theorem norm_inv_leviHalfModulus_le_one (b : (succBlockShape m h).Levi F.Carrier) {d : ℕ}
    (h0 : ((F.canonicalTopologicalData.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ d)
    (h1 : ((F.canonicalTopologicalData.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) =
      ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ d)⁻¹) :
    ‖((F.canonicalTopologicalData.leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹‖ ≤ 1 := by
  set T := F.canonicalTopologicalData
  have hq : (1 : ℝ) ≤ T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one.le
  have hlm : ((T.leviModulus (succBlockShape m h) b : ℝ≥0) : ℝ) =
      ((T.residueCardinality : ℝ) ^ d) ^ (m 1 + 1) *
        ((T.residueCardinality : ℝ) ^ d) ^ (m 0 + 1) := by
    rw [T.leviModulus_apply]
    simp only [Finset.prod_filter, Fin.prod_univ_two]
    simp only [Fin.isValue, lt_self_iff_false, ite_false, Fin.zero_lt_one, ite_true,
      not_lt_zero, mul_one, one_mul]
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow]
    change ((T.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) ^ (m 1 + 1) /
      ((T.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) ^ (m 0 + 1) = _
    rw [h0, h1, inv_pow, div_inv_eq_mul]
  have hone : (1 : ℝ) ≤ T.leviModulus (succBlockShape m h) b := by
    rw [hlm]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_pow₀ hq))
      (one_le_pow₀ (one_le_pow₀ hq))
  rw [T.leviHalfModulus_apply, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  refine inv_le_one_of_one_le₀ ?_
  rw [Real.coe_sqrt]
  exact Real.one_le_sqrt.mpr hone

/-- `(q^d)^(-u) = (q^(-u))^d`. -/
theorem residue_pow_rpow_neg (d : ℕ) (u : ℝ) :
    ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ d) ^ (-u) =
      ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-u)) ^ d := by
  have hq0 : (0 : ℝ) ≤ F.canonicalTopologicalData.residueCardinality := Nat.cast_nonneg _
  rw [← Real.rpow_natCast (F.canonicalTopologicalData.residueCardinality : ℝ) d,
    ← Real.rpow_natCast ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-u)) d,
    ← Real.rpow_mul hq0, ← Real.rpow_mul hq0, mul_comm]

/-- **Pointwise bound.** If `u(x) = q k` with `k ∈ K₀`, the blocks of `q` bounded by `d`,
`|det q_0| = q^d` and `|det q_1| = q^(-d)`, and the untwisted block tensors of the values
of `f` on `K₀` grow at most like `C B^e`, then `|f(u(x))(ℓ) ψ(x)| ≤ C (B q^(-2u))^d`. -/
theorem norm_integrand_le (ψ : UnitaryAdditiveCharacter F.Carrier)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℝ)
    (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
    (ϖ : F.Carrierˣ) (Bp C : ℝ)
    (hC : ∀ k ∈ integralOpen F t, ∀ (e : ℕ) (b : (succBlockShape m h).Levi F.Carrier),
      (∀ i, IsEntryBounded ϖ e (b i)) →
        ‖tensorContraction ell ((succBlockShape m h).blockTensor τ b
          (sectionEval F h (twoBlockOppositeTwistBlocks F m τ u) f k))‖ ≤ C * Bp ^ e)
    (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (q : (succBlockShape m h).oppositeParabolic F.Carrier) (k : GeneralLinear (t + 1) F.Carrier)
    (d : ℕ) (hk : k ∈ integralOpen F t) (hx : upperRadical h F.Carrier x = q * k)
    (hb : ∀ i, IsEntryBounded ϖ d ((succBlockShape m h).oppositeLeviProjection F.Carrier q i))
    (h0 : ((F.canonicalTopologicalData.determinantNorm (m 0 + 1)
        ((succBlockShape m h).oppositeLeviProjection F.Carrier q 0) : ℝ≥0) : ℝ) =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ d)
    (h1 : ((F.canonicalTopologicalData.determinantNorm (m 1 + 1)
        ((succBlockShape m h).oppositeLeviProjection F.Carrier q 1) : ℝ≥0) : ℝ) =
      ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ d)⁻¹) :
    ‖integrand ψ ell f 1 x‖ ≤
      C * (Bp * ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-u) *
        (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-u))) ^ d := by
  set T := F.canonicalTopologicalData
  set b := (succBlockShape m h).oppositeLeviProjection F.Carrier q with hbdef
  have hq0 : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (Nat.zero_lt_one.trans T.residueCardinality_gt_one)
  have hhalf := norm_inv_leviHalfModulus_le_one F h b h0 h1
  have htc := hC k hk d b hb
  have hpos0 : (0 : ℝ) < ((T.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) := by
    rw [h0]
    positivity
  have hpos1 : (0 : ℝ) < ((T.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) := by
    rw [h1]
    positivity
  have htw0 : ‖((((T.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) : ℂ) ^ (-(u : ℂ)))‖ =
      ((T.residueCardinality : ℝ) ^ (-u)) ^ d := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos0, h0, Complex.neg_re, Complex.ofReal_re,
      residue_pow_rpow_neg]
  have htw1 : ‖((((T.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) : ℂ) ^ (u : ℂ))‖ =
      ((T.residueCardinality : ℝ) ^ (-u)) ^ d := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos1, h1, Complex.ofReal_re,
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), residue_pow_rpow_neg]
  rw [integrand_def, norm_mul, norm_positiveKernel, mul_one, mul_one, hx,
    scalarSection_covariant ell f q hbdef.symm k 1, one_mul, scalarSection_def,
    tensorContraction_blockTensor_twist F h τ u ell b]
  simp only [norm_mul]
  rw [htw0, htw1]
  calc
    _ ≤ 1 * (((T.residueCardinality : ℝ) ^ (-u)) ^ d * ((T.residueCardinality : ℝ) ^ (-u)) ^ d *
        (C * Bp ^ d)) :=
      mul_le_mul hhalf (mul_le_mul_of_nonneg_left htc (by positivity)) (by positivity) zero_le_one
    _ = _ := by
      rw [mul_pow, mul_pow]
      ring

end Bounds

section Integrability

/-- **Integrability at the identity.** Under the uniform growth bound on `K₀` and a lower
Iwasawa factorization of every `u(x)` controlled by a box exponent, the integrand at the
identity is integrable as soon as `B q^(-2u) q^(ab) < 1`. -/
theorem integrable_integrand_one (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)) (u : ℝ)
    (ell : ∀ i, W i →ₗ[ℂ] ℂ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
    (Bp C : ℝ) (hC0 : 0 ≤ C) (hBp : 0 ≤ Bp)
    (hC : ∀ k ∈ integralOpen F t, ∀ (e : ℕ) (b : (succBlockShape m h).Levi F.Carrier),
      (∀ i, IsEntryBounded (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
        e (b i)) →
        ‖tensorContraction ell ((succBlockShape m h).blockTensor τ b
          (sectionEval F h (twoBlockOppositeTwistBlocks F m τ u) f k))‖ ≤ C * Bp ^ e)
    (hfac : ∀ x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier,
      ∃ (q : (succBlockShape m h).oppositeParabolic F.Carrier)
        (k : GeneralLinear (t + 1) F.Carrier) (d : ℕ),
        k ∈ integralOpen F t ∧ upperRadical h F.Carrier x = q * k ∧
          x ∈ box F (m 0 + 1) (m 1 + 1) d ∧
          (∀ i, IsEntryBounded
            (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) d
            ((succBlockShape m h).oppositeLeviProjection F.Carrier q i)) ∧
          ((F.canonicalTopologicalData.determinantNorm (m 0 + 1)
              ((succBlockShape m h).oppositeLeviProjection F.Carrier q 0) : ℝ≥0) : ℝ) =
            (F.canonicalTopologicalData.residueCardinality : ℝ) ^ d ∧
          ((F.canonicalTopologicalData.determinantNorm (m 1 + 1)
              ((succBlockShape m h).oppositeLeviProjection F.Carrier q 1) : ℝ≥0) : ℝ) =
            ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ d)⁻¹)
    (hs : Bp * ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-u) *
        (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-u)) *
        (F.canonicalTopologicalData.residueCardinality : ℝ) ^ ((m 0 + 1) * (m 1 + 1)) < 1) :
    Integrable (integrand ψ ell f 1) (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) := by
  set T := F.canonicalTopologicalData
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  have : SigmaCompactSpace F.Carrier := T.sigmaCompactSpace
  have : SigmaFinite ν.measure := inferInstance
  have hcont : Continuous (integrand ψ ell f 1) := by
    have hfun : integrand ψ ell f 1 = fun x =>
        tensorContraction ell (sectionEval F h (twoBlockOppositeTwistBlocks F m τ u) f
          (upperRadical h F.Carrier x)) * positiveKernel ψ x := by
      funext x
      rw [integrand_def, scalarSection_one, mul_one]
    rw [hfun]
    exact ((((Induction.eval_isLocallyConstant _ _ f).comp (tensorContraction ell)).comp_continuous
      (continuous_upperRadical h F.Carrier)).continuous).mul (continuous_positiveKernel ψ)
  refine integrable_of_forall_exists_mem_box hcont.aestronglyMeasurable
    (box F (m 0 + 1) (m 1 + 1)) (measurableSet_box F _ _)
    (M := ν.measure (T.Integers : Set F.Carrier) ^ ((m 0 + 1) * (m 1 + 1)))
    (Q := (T.residueCardinality : ℝ≥0∞) ^ ((m 0 + 1) * (m 1 + 1))) ?_
    (fun e => (rectangularMeasure_box F ν _ _ e).le) hC0
    (s := Bp * ((T.residueCardinality : ℝ) ^ (-u) * (T.residueCardinality : ℝ) ^ (-u)))
    (by positivity) ?_ ?_
  · exact ENNReal.pow_ne_top (T.isCompact_integers.measure_lt_top).ne
  · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_one]
    exact hs
  · intro x
    obtain ⟨q, k, d, hk, hx, hbox, hb, h0, h1⟩ := hfac x
    exact ⟨d, hbox, norm_integrand_le F h ψ τ u ell f _ Bp C hC x q k d hk hx hb h0 h1⟩

end Integrability

section Assembly

/-- **Assembly.** Given the lower Iwasawa factorization of every `u(x)` controlled by a box
exponent, there is a real bound beyond which every section of the twisted induction has an
absolutely integrable integrand at every ambient element. -/
theorem exists_bound_isAbsIntegrable_of_factorization (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hfac : ∀ x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier,
      ∃ (q : (succBlockShape m h).oppositeParabolic F.Carrier)
        (k : GeneralLinear (t + 1) F.Carrier) (d : ℕ),
        k ∈ integralOpen F t ∧ upperRadical h F.Carrier x = q * k ∧
          x ∈ box F (m 0 + 1) (m 1 + 1) d ∧
          (∀ i, IsEntryBounded
            (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) d
            ((succBlockShape m h).oppositeLeviProjection F.Carrier q i)) ∧
          ((F.canonicalTopologicalData.determinantNorm (m 0 + 1)
              ((succBlockShape m h).oppositeLeviProjection F.Carrier q 0) : ℝ≥0) : ℝ) =
            (F.canonicalTopologicalData.residueCardinality : ℝ) ^ d ∧
          ((F.canonicalTopologicalData.determinantNorm (m 1 + 1)
              ((succBlockShape m h).oppositeLeviProjection F.Carrier q 1) : ℝ≥0) : ℝ) =
            ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ d)⁻¹) :
    ∃ C : ℝ, ∀ u : ℝ, C < u →
      ∀ f : Sections F h (twoBlockOppositeTwistBlocks F m τ u),
        IsAbsIntegrable ψ (fun i => (ell i).val) (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) f := by
  set T := F.canonicalTopologicalData
  choose B hB hg using fun i => exists_functional_growth F ψ (τ i) (hτ i) (ell i)
  have hq1 : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  have hq0 : (0 : ℝ) < T.residueCardinality := zero_lt_one.trans hq1
  have hBpos : 0 < ∏ i, B i := Finset.prod_pos fun i _ => zero_lt_one.trans_le (hB i)
  refine ⟨(Real.logb T.residueCardinality (∏ i, B i) +
    (((m 0 + 1) * (m 1 + 1) : ℕ) : ℝ)) / 2, fun u hu f g => ?_⟩
  unfold IsAbsIntegrableAt
  rw [show g = 1 * g from (one_mul g).symm, ← integrand_inducedRep]
  obtain ⟨C, hC0, hC⟩ := exists_integral_growth F h τ (twoBlockOppositeTwistBlocks F m τ u)
    (fun i => (ell i).val) (LocalFactor.PadicAbelian.uniformizerUnit T) B
    (fun i => zero_le_one.trans (hB i)) hg (inducedRep F h _ g f)
  refine integrable_integrand_one F h ψ ν τ u _ _ (∏ i, B i) C hC0 hBpos.le hC hfac ?_
  rw [← Real.rpow_logb hq0 hq1.ne' hBpos, ← Real.rpow_natCast, ← Real.rpow_add hq0,
    ← Real.rpow_add hq0, ← Real.rpow_add hq0]
  exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)

end Assembly

/-- **JPSS 1983, Section (4.6).** Ordinary absolute convergence of the two-block Jacquet
integral for opposite real twists `(τ_1 |det|^(-u), τ_2 |det|^u)` and all large real `u`. -/
theorem _root_.Langlands.RankinSelberg.twoBlockJacquetConvergence :
    TwoBlockJacquetConvergenceStatement.{uF, uW} := by
  intro p _ F ψ ν t m h W _ _ τ hτ ell _
  exact exists_bound_isAbsIntegrable_of_factorization F h ψ ν.val τ hτ ell
    (exists_radical_factorization F h)

end Padic

end Langlands.RankinSelberg.TwoBlockConvergence
