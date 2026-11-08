import Langlands.Representation.RankinSelberg.SphericalWhittakerFormula
import Langlands.Representation.RankinSelberg.SphericalPairTorusReduction
import Langlands.Representation.RankinSelberg.SchurPairSummability
import Langlands.Representation.RankinSelberg.JacobiTrudiPadding
import Langlands.Representation.RankinSelberg.SymmetricDominant
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.RankinSelberg.UnramifiedPairStatement
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionReduction
import Langlands.Representation.Conductor.SphericalIntegrals

/-!
# Torus coefficients of the unramified unequal-rank integrand
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.UnramifiedPairTorus

open GeneralLinear GeneralLinear.Iwasawa GeneralLinear.Spherical Whittaker Conductor
  HarmonicAnalysis QuotientIntegration QuotientTorusEnvelope UnramifiedWhittaker
  Correspondence Unramified

universe uF uV uW

/-! ### Zero extension of weights -/

section Weights

/-- Extend a weight of rank `n + 1` by `d` zero coordinates. -/
def extendWeight (n d : ℕ) (lam : Fin (n + 1) → ℤ) : Fin (n + d + 1) → ℤ :=
  fun i => if h : i.val < n + 1 then lam ⟨i.val, h⟩ else 0

theorem padWeight_apply {m : ℕ} (α : Fin m → ℤ) (k : ℕ) (j : Fin (m + k)) :
    padWeight α k j = if h : j.val < m then α ⟨j.val, h⟩ else 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [padWeight, i.isLt]
  · simp [padWeight]

theorem jacobiTrudiIn_cast (σ R : Type*) [Fintype σ] [DecidableEq σ] [CommRing R]
    {m m' : ℕ} (h : m = m') (β : Fin m → ℤ) (β' : Fin m' → ℤ)
    (hβ : ∀ i : Fin m', β' i = β (Fin.cast h.symm i)) :
    jacobiTrudiIn σ R β' = jacobiTrudiIn σ R β := by
  subst h
  have : β' = β := funext fun i => by simpa using hβ i
  rw [this]

theorem jacobiTrudiIn_extendWeight (σ R : Type*) [Fintype σ] [DecidableEq σ] [CommRing R]
    (n d : ℕ) (lam : Fin (n + 1) → ℤ) :
    jacobiTrudiIn σ R (extendWeight n d lam) = jacobiTrudiIn σ R lam := by
  rw [← jacobiTrudiIn_padWeight σ R lam d]
  apply jacobiTrudiIn_cast σ R (by omega)
  intro i
  rw [padWeight_apply, extendWeight]
  rfl

theorem isPartitionExponent_of_antitone_extendWeight {n d : ℕ} {lam : Fin (n + 1) → ℤ}
    (h : Antitone (extendWeight n (d + 1) lam)) : IsPartitionExponent lam := by
  have hval (i : Fin (n + 1)) :
      extendWeight n (d + 1) lam ⟨i.val, by omega⟩ = lam i := by
    simp [extendWeight, i.isLt]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [← hval i, ← hval j]
    exact h (Fin.mk_le_mk.mpr hij)
  · have hz : extendWeight n (d + 1) lam ⟨n + 1, by omega⟩ = 0 := by
      simp [extendWeight]
    rw [← hval i, ← hz]
    exact h (Fin.mk_le_mk.mpr (by omega))

theorem antitone_extendWeight {n d : ℕ} {lam : Fin (n + 1) → ℤ}
    (h : IsPartitionExponent lam) : Antitone (extendWeight n d lam) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  by_cases hj : j.val < n + 1
  · have hi : i.val < n + 1 := by omega
    simp only [extendWeight, dite_eq_left hi, dite_eq_left hj]
    exact h.1 (Fin.mk_le_mk.mpr hij')
  · simp only [extendWeight, dite_eq_right hj]
    split_ifs
    · exact h.2 _
    · exact le_rfl

theorem sum_mul_extendWeight (n d : ℕ) (c : ℕ → ℤ) (lam : Fin (n + 1) → ℤ) :
    ∑ i : Fin (n + d + 1), c i * extendWeight n d lam i = ∑ i : Fin (n + 1), c i * lam i := by
  let g : ℕ → ℤ := fun m => c m * if h : m < n + 1 then lam ⟨m, h⟩ else 0
  have h1 : ∑ i : Fin (n + d + 1), c i * extendWeight n d lam i =
      ∑ m ∈ Finset.range (n + d + 1), g m :=
    Fin.sum_univ_eq_sum_range g (n + d + 1)
  have h2 : ∑ i : Fin (n + 1), c i * lam i = ∑ m ∈ Finset.range (n + 1), g m := by
    rw [← Fin.sum_univ_eq_sum_range g (n + 1)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [g, dite_eq_left i.isLt]
  rw [h1, h2]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
  intro m _ hm
  have : ¬ m < n + 1 := by simpa using hm
  simp only [g, dite_eq_right this, mul_zero]

end Weights

/-! ### Real exponent identities -/

section Exponents

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) {x : ℝ} (hx : x ≠ 0) :
    ∏ i ∈ s, x ^ f i = x ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

/-- `∑_(i<j) (λ_i - λ_j) = ∑_i (n - 2i) λ_i` on `Fin (n + 1)`. -/
theorem sum_pairs_sub (n : ℕ) (lam : Fin (n + 1) → ℤ) :
    ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      (lam i - lam j) = ∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i := by
  have hswap : ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      lam j = ∑ j : Fin (n + 1), ∑ _i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i < j),
      lam j := by
    apply Finset.sum_comm'
    intro i j
    simp
  have hcard1 (i : Fin (n + 1)) :
      ((Finset.univ.filter (fun j : Fin (n + 1) => i < j)).card : ℤ) = n - i := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    rw [show n + 1 - 1 - (i : ℕ) = n - i by omega, Nat.cast_sub hi]
  have hcard2 (j : Fin (n + 1)) :
      ((Finset.univ.filter (fun i : Fin (n + 1) => i < j)).card : ℤ) = j := by
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  simp only [Finset.sum_sub_distrib]
  rw [hswap]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard1, hcard2]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Exponents

/-! ### The zero-dimensional rectangular variable -/

section Dirac

variable {F : Type*} [Field F] [TopologicalSpace F]

theorem unequalRankIntegrand_zero_rows (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ) (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) (x : Matrix (Fin 0) (Fin (n + 1)) F) :
    unequalRankIntegrand ψ abv 0 k W W' s x = unequalRankIntegrand ψ abv 0 k W W' s 0 := by
  rw [Subsingleton.elim x 0]

theorem unequalRankConverges_of_integrable (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (h : Integrable (unequalRankIntegrand ψ abv 0 k W W' s 0) μ) :
    UnequalRankConverges ψ abv 0 k μ (Measure.dirac 0) W W' s := by
  unfold UnequalRankConverges
  simp_rw [unequalRankIntegrand_zero_rows ψ abv k W W' s]
  exact h.comp_fst _

theorem unequalRankIntegral_dirac (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv 0 k μ (Measure.dirac 0) W W' s =
      ∫ q, unequalRankIntegrand ψ abv 0 k W W' s 0 q ∂μ := by
  unfold unequalRankIntegral
  simp_rw [unequalRankIntegrand_zero_rows ψ abv k W W' s]
  simp

end Dirac

/-! ### The integrand on the canonical local field -/

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance pairFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance pairFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance pairFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- `diag(y, 1_d)` is integral when `y` is. -/
theorem appendIdentity_mem_integralSubgroup (n d : ℕ)
    {y : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hy : y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n) :
    appendIdentity n d y ∈
      integralSubgroup (ValuativeRel.valuation F.Carrier).integer (n + d) := by
  rw [mem_integralSubgroup] at hy ⊢
  have hent : ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      (∀ i j, g i j ∈ (ValuativeRel.valuation F.Carrier).integer) →
      ∀ i j, appendIdentity n d g i j ∈ (ValuativeRel.valuation F.Carrier).integer := by
    intro g hg i j
    rw [appendIdentity_entry]
    split_ifs
    · exact hg _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hent y hy.1, ?_⟩
  rw [← map_inv]
  exact hent y⁻¹ hy.2

/-- The unequal-rank function with no rectangular rows is right invariant under the
integral group, when both Whittaker functions are. -/
theorem unequalRankFunction_mul_integral (ψ : UnitaryAdditiveCharacter F.Carrier)
    (abv : AbsoluteValue F.Carrier ℝ)
    (habv : ∀ x : F.Carrier, ValuativeRel.valuation F.Carrier x = 1 → abv x = 1)
    {n : ℕ} (k : ℕ) (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (hW : ∀ g, ∀ y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer
      (n + (0 + k + 1)), W.val (g * y) = W.val g)
    (hW' : ∀ g, ∀ y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n,
      W'.val (g * y) = W'.val g)
    (s : ℂ) (x : Matrix (Fin 0) (Fin (n + 1)) F.Carrier)
    (g y : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hy : y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n) :
    unequalRankFunction ψ abv 0 k W W' s x (g * y) =
      unequalRankFunction ψ abv 0 k W W' s x g := by
  unfold unequalRankFunction
  rw [unequalRankMatrix_zero_rows, unequalRankMatrix_zero_rows, map_mul,
    hW _ _ (appendIdentity_mem_integralSubgroup F n _ hy), hW' _ _ hy,
    determinantWeight_mul_integral habv g y hy]

theorem isOpen_integralSubgroup (n : ℕ) :
    IsOpen (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
  rw [← levelSubgroup_zero]
  exact (levelOpenSubgroup F.Carrier n 0).isOpen

/-- The descended integrand is continuous. -/
theorem continuous_unequalRankIntegrand (ψ : UnitaryAdditiveCharacter F.Carrier)
    (abv : AbsoluteValue F.Carrier ℝ)
    (habv : ∀ x : F.Carrier, ValuativeRel.valuation F.Carrier x = 1 → abv x = 1)
    {n : ℕ} (k : ℕ) (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (hW : ∀ g, ∀ y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer
      (n + (0 + k + 1)), W.val (g * y) = W.val g)
    (hW' : ∀ g, ∀ y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n,
      W'.val (g * y) = W'.val g)
    (s : ℂ) (x : Matrix (Fin 0) (Fin (n + 1)) F.Carrier) :
    Continuous (unequalRankIntegrand ψ abv 0 k W W' s x) := by
  have hf : Continuous (unequalRankFunction ψ abv 0 k W W' s x) :=
    SquareIntegrableWhittakerRestriction.continuous_of_rightInvariant _
      (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n)
      (isOpen_integralSubgroup F n)
      (fun g y hy => unequalRankFunction_mul_integral F ψ abv habv k W W' hW hW' s x g y hy)
  exact hf.quotient_lift _




/-! ### Normalizations -/

/-- Two uniformizing elements have the same valuation. -/
theorem valuation_eq_of_isUniformizingElement {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) {ϖ ϖ' : Kˣ}
    (h : IsUniformizingElement v ϖ) (h' : IsUniformizingElement v ϖ') :
    v (ϖ' : K) = v (ϖ : K) := by
  obtain ⟨m, hm⟩ := h.2 (ϖ' : K) ϖ'.ne_zero
  obtain ⟨m', hm'⟩ := h'.2 (ϖ : K) ϖ.ne_zero
  have h0 : 0 < v (ϖ : K) := Langlands.GeneralLinear.Iwasawa.valuation_pos v ϖ
  have hmm : m * m' = 1 := by
    have : v (ϖ : K) ^ (1 : ℤ) = v (ϖ : K) ^ (m * m') := by
      rw [zpow_one, zpow_mul, ← hm, ← hm']
    exact ((zpow_right_injective₀ h0 h.1.ne) this).symm
  have hpos : 0 < m := by
    have := h'.1
    rw [hm] at this
    exact (zpow_lt_one_iff_right_of_lt_one₀ h0 h.1).mp this
  rw [hm, Int.eq_one_of_mul_eq_one_right hpos.le hmm, zpow_one]

/-- Under Jacquet's normalization the canonical uniformizer has absolute value `q⁻¹`. -/
theorem abv_uniformizerUnit {q : ℕ} {abv : AbsoluteValue F.Carrier ℝ} {ϖ : F.Carrierˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    (habv : abv (ϖ : F.Carrier) = (q : ℝ)⁻¹)
    (hunit : ∀ x : F.Carrier, ValuativeRel.valuation F.Carrier x = 1 → abv x = 1) :
    abv (F.canonicalTopologicalData.uniformizerUnit : F.Carrier) = (q : ℝ)⁻¹ := by
  set ϖ₀ := F.canonicalTopologicalData.uniformizerUnit
  have hv := valuation_eq_of_isUniformizingElement (ValuativeRel.valuation F.Carrier) hϖ
    (Langlands.Unramified.uniformizerUnit_isUniformizingElement F)
  have hu : ValuativeRel.valuation F.Carrier ((ϖ₀ : F.Carrier) / ϖ) = 1 := by
    rw [map_div₀, hv, div_self]
    exact (Valuation.ne_zero_iff _).mpr ϖ.ne_zero
  have h1 := hunit _ hu
  rw [map_div₀, div_eq_one_iff_eq] at h1
  · rw [h1, habv]
  · rw [habv]
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    intro h
    exact absurd (inv_eq_zero.mp h) (by
      intro hq0
      have := abv.pos (Units.ne_zero ϖ)
      rw [habv, hq0, inv_zero] at this
      exact lt_irrefl 0 this)

theorem residueCardinality_real_pos :
    (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
  have := F.canonicalTopologicalData.residueCardinality_gt_one
  exact_mod_cast (lt_trans Nat.zero_lt_one this)

theorem normalizedAbs_uniformizerUnit_div (a b : ℤ) :
    F.canonicalTopologicalData.normalizedAbs
        ((F.canonicalTopologicalData.uniformizerUnit ^ a /
          F.canonicalTopologicalData.uniformizerUnit ^ b : F.Carrierˣ) : F.Carrier) =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(a - b)) := by
  rw [div_eq_mul_inv, ← _root_.zpow_sub, LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs]

/-- The inverse modulus at the canonical torus element. -/
theorem density_uniformizerUnit {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    density F F.canonicalTopologicalData F.canonicalTopologicalData.uniformizerUnit lam =
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i) := by
  have hq := (residueCardinality_real_pos F).ne'
  unfold density
  simp only [normalizedAbs_uniformizerUnit_div]
  rw [Finset.prod_congr rfl (fun i _ => prod_zpow_eq_zpow_sum _ _ hq),
    prod_zpow_eq_zpow_sum _ _ hq, ← zpow_neg, ← sum_pairs_sub]
  simp only [Finset.sum_neg_distrib, neg_neg]


theorem scalar_identity (q : ℕ) (hq : 0 < q) (k : ℕ) (a : ℤ) (S : ℕ) (s : ℂ) :
    (((q : ℝ) ^ a : ℝ) : ℂ) *
      ((((Real.sqrt q : ℝ) : ℂ) ^ (-(a + ((k : ℤ) + 1) * (S : ℤ))) *
        ((Real.sqrt q : ℝ) : ℂ) ^ (-a)) *
      (((((q : ℝ)⁻¹) ^ S : ℝ) : ℂ) ^ (s - ((0 + k + 1 : ℕ) : ℂ) / 2))) =
    ((q : ℂ) ^ (-s)) ^ S := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : ((Real.sqrt q : ℝ) : ℂ) = Complex.exp ((Real.log q : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq', Complex.ofReal_exp]
    push_cast
    ring_nf
  have hqa : (((q : ℝ) ^ a : ℝ) : ℂ) = Complex.exp (a * (Real.log q : ℂ)) := by
    rw [Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hq']
    norm_cast
  have hdet : ((((q : ℝ)⁻¹) ^ S : ℝ) : ℂ) ^ (s - ((0 + k + 1 : ℕ) : ℂ) / 2) =
      Complex.exp ((-(S : ℂ) * (Real.log q : ℂ)) * (s - ((0 + k + 1 : ℕ) : ℂ) / 2)) := by
    have hpos : (0 : ℝ) < ((q : ℝ)⁻¹) ^ S := by positivity
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le,
      Real.log_pow, Real.log_inv]
    push_cast
    ring_nf
  have hqs : (q : ℂ) ^ (-s) = Complex.exp ((Real.log q : ℂ) * (-s)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq'.ne'), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hq'.le]
  rw [hqa, hsq, hdet, hqs, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring


/-! ### Torus coefficients of the spherical pair integrand -/

theorem sum_halfModulus_extendWeight (n d : ℕ) (lam : Fin (n + 1) → ℤ) :
    ∑ i : Fin (n + d + 1), (((n + d : ℕ) : ℤ) - 2 * (i : ℤ)) * extendWeight n d lam i =
      ∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i + (d : ℤ) * ∑ i, lam i := by
  refine (sum_mul_extendWeight n d (fun m => ((n + d : ℕ) : ℤ) - 2 * (m : ℤ)) lam).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem satakeSchur_natWeight {m : ℕ} (χ : Fin (m + 1) → QuasiCharacter F)
    (α : Fin (m + 1) → ℕ) (hα : Antitone α) :
    satakeSchur (characterValues F χ) (fun i => (α i : ℤ)) =
      jacobiTrudiValue (unramifiedClass F χ) α := by
  rw [satakeSchur_eq_eval_jacobiTrudi _ _ (fun i j hij => by exact_mod_cast hα hij)
    (fun i => by positivity)]
  rfl

theorem satakeSchur_extendWeight {n d : ℕ} (χ : Fin (n + d + 1) → QuasiCharacter F)
    (α : Fin (n + 1) → ℕ) (hα : Antitone α) :
    satakeSchur (characterValues F χ) (extendWeight n d (fun i => (α i : ℤ))) =
      jacobiTrudiValue (unramifiedClass F χ) α := by
  have hpart : IsPartitionExponent (fun i => (α i : ℤ)) :=
    ⟨fun i j hij => Nat.cast_le.mpr (hα hij), fun i => Nat.cast_nonneg _⟩
  have hnonneg : ∀ i, 0 ≤ extendWeight n d (fun i => (α i : ℤ)) i := by
    intro i
    unfold extendWeight
    split_ifs
    · positivity
    · exact le_rfl
  rw [satakeSchur_eq_eval_jacobiTrudi _ _ (antitone_extendWeight hpart) hnonneg]
  change MvPolynomial.eval _ (jacobiTrudiIn (Fin (n + d + 1)) ℂ _) = _
  rw [jacobiTrudiIn_extendWeight]
  rfl

theorem abv_det_torus_natWeight {q : ℕ} {abv : AbsoluteValue F.Carrier ℝ}
    (habv : abv (F.canonicalTopologicalData.uniformizerUnit : F.Carrier) = (q : ℝ)⁻¹)
    {n : ℕ} (α : Fin (n + 1) → ℕ) :
    abv (Matrix.det (torus F.canonicalTopologicalData.uniformizerUnit
      (fun i => (α i : ℤ))).val) = ((q : ℝ)⁻¹) ^ (∑ i, α i) := by
  rw [torus_val, Matrix.det_diagonal, map_prod]
  simp only [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, habv]
  rw [Finset.prod_pow_eq_pow_sum]

section Coefficient

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (abv : AbsoluteValue F.Carrier ℝ)
  {n k : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W]
  [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (ℓ : glFunctionals ψ (n + (0 + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
  (w : SphericalTest π ℓ) (w' : SphericalTest σ ℓ') (s : ℂ)

/-- The literal torus coefficient of the descended integrand. -/
theorem torusCoefficient_apply (ϖ : F.Carrierˣ) (lam : Fin (n + 1) → ℤ) :
    torusCoefficient F F.canonicalTopologicalData ϖ
        (unequalRankIntegrand ψ abv 0 k w.val.val.val w'.val.val.val s 0) lam =
      (density F F.canonicalTopologicalData ϖ lam : ℂ) *
        (sphericalTestFunction π ℓ w (torus ϖ (extendWeight n (0 + k + 1) lam)) *
          sphericalTestFunction σ ℓ' w' (torus ϖ lam) *
          determinantWeight abv (torus ϖ lam) (s - ((0 + k + 1 : ℕ) : ℂ) / 2)) := by
  simp only [torusCoefficient, leftQuotientMap_apply, unequalRankIntegrand_mk,
    unequalRankMatrix_zero_rows, SquareIntegrableWhittakerRestriction.appendIdentity_torus]
  rfl

/-- Off partition exponents the torus coefficient vanishes. -/
theorem torusCoefficient_eq_zero (hψ : HasIntegerConductor ψ) (lam : Fin (n + 1) → ℤ)
    (hlam : ¬ IsPartitionExponent lam) :
    torusCoefficient F F.canonicalTopologicalData F.canonicalTopologicalData.uniformizerUnit
        (unequalRankIntegrand ψ abv 0 k w.val.val.val w'.val.val.val s 0) lam = 0 := by
  have hW : sphericalTestFunction π ℓ w
      (torus F.canonicalTopologicalData.uniformizerUnit (extendWeight n (0 + k + 1) lam)) = 0 :=
    eval_torus_eq_zero_of_not_antitone (Langlands.Unramified.uniformizerUnit_isUniformizingElement F)
      (sphericalTestFunction_equivariance π ℓ w)
      (fun g y hy => sphericalTestFunction_right_invariant π ℓ w ⟨y, hy⟩ g)
      (standardCharacter_nondegenerate F ψ hψ)
      (fun h => hlam (isPartitionExponent_of_antitone_extendWeight h))
  rw [torusCoefficient_apply, hW]
  simp

/-- On natural partitions the torus coefficient is the Schur pair term at `t = q^(-s)`:
the inverse modulus, both half moduli and `|det|^(s - (k+1)/2)` combine to `q^(-s |α|)`. -/
theorem torusCoefficient_natWeight (hψ : HasIntegerConductor ψ)
    (χ : Fin (n + (0 + k + 1) + 1) → QuasiCharacter F) (χ' : Fin (n + 1) → QuasiCharacter F)
    (hπ : IsUnramifiedGenericConstituent F ψ π χ) (hσ : IsUnramifiedGenericConstituent F ψ σ χ')
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (habv : abv (F.canonicalTopologicalData.uniformizerUnit : F.Carrier) =
      (F.canonicalTopologicalData.residueCardinality : ℝ)⁻¹)
    (α : Fin (n + 1) → ℕ) (hα : Antitone α) :
    torusCoefficient F F.canonicalTopologicalData F.canonicalTopologicalData.uniformizerUnit
        (unequalRankIntegrand ψ abv 0 k w.val.val.val w'.val.val.val s 0)
        (fun i => (α i : ℤ)) =
      schurPairTerm (unramifiedClass F χ) (unramifiedClass F χ')
        ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-s)) α := by
  have hpart : IsPartitionExponent (fun i => (α i : ℤ)) :=
    ⟨fun i j hij => Nat.cast_le.mpr (hα hij), fun i => Nat.cast_nonneg _⟩
  have hext : IsPartitionExponent (extendWeight n (0 + k + 1) (fun i => (α i : ℤ))) := by
    refine ⟨antitone_extendWeight hpart, fun i => ?_⟩
    unfold extendWeight
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl
  rw [torusCoefficient_apply, density_uniformizerUnit,
    sphericalTest_torus_schur F π ψ hψ χ hπ ℓ hℓ w _ hext,
    inverseSphericalTest_torus_schur F σ ψ hψ χ' hσ ℓ' hℓ' w' _ hpart,
    satakeSchur_extendWeight F χ α hα, satakeSchur_natWeight F χ' α hα]
  unfold determinantWeight halfModulus schurPairTerm
  rw [abv_det_torus_natWeight F habv α, sum_halfModulus_extendWeight]
  have hS : (∑ i, (α i : ℤ)) = ((∑ i, α i : ℕ) : ℤ) := by push_cast; rfl
  have hd : ((0 + k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  simp only [hS, hd]
  rw [← scalar_identity F.canonicalTopologicalData.residueCardinality
    (lt_trans Nat.zero_lt_one F.canonicalTopologicalData.residueCardinality_gt_one) k
    (∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * (α i : ℤ)) (∑ i, α i) s]
  ring

end Coefficient

end Padic

/-! ### The actual pair integral as a sum over partitions -/

/-- The actual unequal-rank integral of the normalized spherical vectors, with the
zero-dimensional rectangular variable carrying the unit point mass, converges absolutely
and equals the series of Schur pair terms over natural partitions at `t = q^(-s)`, as
soon as that series converges absolutely. -/
theorem pairIntegral_eq_tsum :
    ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n k : ℕ)
      {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
      (χ : Fin (n + (0 + k + 1) + 1) → QuasiCharacter F) (χ' : Fin (n + 1) → QuasiCharacter F)
      (q : ℕ)
      (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
      (abv : AbsoluteValue F.Carrier ℝ) (ϖ : F.Carrierˣ)
      (μ : letI := F.canonicalTopologicalData.topology
        letI := borel (LeftUnipotentQuotient n F.Carrier)
        Measure (LeftUnipotentQuotient n F.Carrier)),
      IsUnramifiedGenericConstituent F ψ π χ → IsUnramifiedGenericConstituent F ψ σ χ' →
      letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := borel F.Carrier
      letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
      letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (upperUnipotent (n + 1) F.Carrier)
      letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (LeftUnipotentQuotient n F.Carrier)
      letI := borel (LeftUnipotentQuotient 0 F.Carrier)
      IsJacquetNormalization q ψ abv ϖ μ →
      ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        ∀ (w : SphericalTest π ℓ) (w' : SphericalTest σ ℓ') (s : ℂ),
          Summable (fun α : {α : Fin (n + 1) → ℕ // Antitone α} =>
            ‖schurPairTerm (unramifiedClass F χ) (unramifiedClass F χ') ((q : ℂ) ^ (-s))
              α.val‖) →
          UnequalRankConverges ψ abv 0 k μ (Measure.dirac 0) w.val.val.val w'.val.val.val s ∧
          unequalRankModelIntegral ψ abv 0 k μ (Measure.dirac 0) π σ ℓ ℓ' w.val.val
              w'.val.val s =
            ∑' α : {α : Fin (n + 1) → ℕ // Antitone α},
              schurPairTerm (unramifiedClass F χ) (unramifiedClass F χ') ((q : ℂ) ^ (-s))
                α.val := by
  intro p _ F n k V _ _ W _ _ π σ χ χ' q ψ abv ϖ μ hπ hσ hJ ℓ ℓ' hℓ hℓ' w w' s hsum
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  have hq : q = F.canonicalTopologicalData.residueCardinality := hJ.residueCardinality
  subst hq
  have hψ : HasIntegerConductor ψ := hJ.conductor
  have habv : abv (F.canonicalTopologicalData.uniformizerUnit : F.Carrier) =
      (F.canonicalTopologicalData.residueCardinality : ℝ)⁻¹ :=
    abv_uniformizerUnit F hJ.uniformizer hJ.abv_uniformizer hJ.abv_unit
  have hW : ∀ g, ∀ y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer
      (n + (0 + k + 1)), w.val.val.val.val (g * y) = w.val.val.val.val g :=
    fun g y hy => sphericalTestFunction_right_invariant π ℓ w ⟨y, hy⟩ g
  have hW' : ∀ g, ∀ y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n,
      w'.val.val.val.val (g * y) = w'.val.val.val.val g :=
    fun g y hy => sphericalTestFunction_right_invariant σ ℓ' w' ⟨y, hy⟩ g
  set E := unequalRankIntegrand ψ abv 0 k w.val.val.val w'.val.val.val s 0 with hEdef
  set c := torusCoefficient F F.canonicalTopologicalData
    F.canonicalTopologicalData.uniformizerUnit E with hcdef
  let ι : {α : Fin (n + 1) → ℕ // Antitone α} → (Fin (n + 1) → ℤ) := fun α i => (α.val i : ℤ)
  have hι : Function.Injective ι := by
    intro α β h
    apply Subtype.ext
    funext i
    exact Nat.cast_injective (R := ℤ) (congrFun h i)
  have hcoef : ∀ α, c (ι α) =
      schurPairTerm (unramifiedClass F χ) (unramifiedClass F χ')
        ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-s)) α.val :=
    fun α => torusCoefficient_natWeight F ψ abv π σ ℓ ℓ' w w' s hψ χ χ' hπ hσ hℓ hℓ' habv
      α.val α.property
  have hzero : ∀ lam ∉ Set.range ι, c lam = 0 := by
    intro lam hlam
    apply torusCoefficient_eq_zero F ψ abv π σ ℓ ℓ' w w' s hψ lam
    intro hpart
    apply hlam
    refine ⟨⟨fun i => (lam i).toNat, fun i j hij => Int.toNat_le_toNat (hpart.1 hij)⟩, ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hpart.2 i)
  have hsum' : Summable (fun lam => ‖c lam‖) := by
    rw [← hι.summable_iff (f := fun lam => ‖c lam‖) (fun lam hlam => by
      simp only [hzero lam hlam, norm_zero])]
    simpa only [Function.comp_def, hcoef] using hsum
  have hE : Measurable E :=
    (continuous_unequalRankIntegrand F ψ abv hJ.abv_unit k _ _ hW hW' s 0).measurable
  have hK : ∀ lam y,
      y ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
      E (leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
        (torus F.canonicalTopologicalData.uniformizerUnit lam * y)) =
      E (leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
        (torus F.canonicalTopologicalData.uniformizerUnit lam)) :=
    fun lam y hy => unequalRankFunction_mul_integral F ψ abv hJ.abv_unit k _ _ hW hW' s 0 _ y hy
  obtain ⟨hint, heq⟩ := integrable_integral_eq_tsum_torus F F.canonicalTopologicalData n μ
    hJ.measure F.canonicalTopologicalData.uniformizerUnit
    (uniformizerUnit_isUniformizingElement F) E hE hK hsum'
  refine ⟨unequalRankConverges_of_integrable ψ abv k μ _ _ s hint, ?_⟩
  rw [unequalRankModelIntegral, unequalRankIntegral_dirac, heq,
    ← hι.tsum_eq (fun lam hlam => by
      by_contra h
      exact hlam (hzero lam h))]
  exact tsum_congr hcoef

end Langlands.RankinSelberg.UnramifiedPairTorus
