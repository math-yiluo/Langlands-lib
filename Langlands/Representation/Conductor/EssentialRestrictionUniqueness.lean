import Langlands.Representation.Conductor.SphericalSeparation
import Langlands.Representation.Conductor.SphericalDegree
import Langlands.Representation.Conductor.EssentialScaledUniqueness
import Langlands.Representation.Conductor.EssentialConductorAssembly
import Langlands.Representation.Conductor.JacquetRestrictionInvariance

/-!
# Essential vectors agree on the mirabolic subgroup

On a half-plane of convergence the corank-one integral of a model vector against the
spherical Whittaker function `W(g; x; ψ̄)` is the sum `∑_d c_d(x) q^(-ds)` of the
specialized Laurent degree coefficients. A Laurent series with lower-bounded support
whose sums vanish on an interval `(0, r)` has zero coefficients. Hence, if the
corank-one integrals of a model vector vanish on a real half-line for every `x`, all
its Laurent degree coefficients vanish. The difference of two essential vectors has
this property, so by the separation theorem it vanishes on `diag(GL_(n+1), 1)`, and
therefore on the whole mirabolic subgroup.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Filter Topology Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa

universe uF uV

section Laurent

/-- The constant coefficient of a complex power series whose sums vanish at every
point of an interval `(0, r)` is zero. -/
theorem coeff_zero_eq_zero_of_hasSum_eq_zero {r : ℝ} (hr : 0 < r) {a : ℕ → ℂ}
    (ha : ∀ X : ℝ, 0 < X → X < r → HasSum (fun k => a k * (X : ℂ) ^ k) 0) : a 0 = 0 := by
  set r₀ := r / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hr₀r : r₀ < r := by linarith
  have habs : Summable (fun k => ‖a (k + 1)‖ * r₀ ^ (k + 1)) := by
    have hs : Summable (fun k => a k * (r₀ : ℂ) ^ k) := (ha r₀ hr₀pos hr₀r).summable
    have hn : Summable (fun k => ‖a k * (r₀ : ℂ) ^ k‖) := summable_norm_iff.mpr hs
    have hn' : Summable (fun k => ‖a k‖ * r₀ ^ k) := by
      refine hn.congr (fun k => ?_)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr₀pos.le]
    exact (summable_nat_add_iff 1).mpr hn'
  set T := ∑' k, ‖a (k + 1)‖ * r₀ ^ (k + 1) with hT
  have hbound : ∀ X : ℝ, 0 < X → X < r₀ → ‖a 0‖ ≤ X / r₀ * T := by
    intro X hX hXr
    have hshift := (hasSum_nat_add_iff' 1).mpr (ha X hX (hXr.trans hr₀r))
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, zero_sub] at hshift
    have hsn : Summable (fun k => ‖a (k + 1) * (X : ℂ) ^ (k + 1)‖) :=
      summable_norm_iff.mpr hshift.summable
    have hterm : ∀ k, ‖a (k + 1) * (X : ℂ) ^ (k + 1)‖ ≤
        X / r₀ * (‖a (k + 1)‖ * r₀ ^ (k + 1)) := by
      intro k
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hX.le]
      have hpow : X ^ (k + 1) ≤ X / r₀ * r₀ ^ (k + 1) := by
        have he : X / r₀ * r₀ ^ (k + 1) = r₀ ^ k * X := by
          field_simp
          ring
        rw [he, pow_succ]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX.le hXr.le k) hX.le
      calc ‖a (k + 1)‖ * X ^ (k + 1) ≤ ‖a (k + 1)‖ * (X / r₀ * r₀ ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = X / r₀ * (‖a (k + 1)‖ * r₀ ^ (k + 1)) := by ring
    calc ‖a 0‖ = ‖∑' k, a (k + 1) * (X : ℂ) ^ (k + 1)‖ := by
          rw [hshift.tsum_eq, norm_neg]
      _ ≤ ∑' k, ‖a (k + 1) * (X : ℂ) ^ (k + 1)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, X / r₀ * (‖a (k + 1)‖ * r₀ ^ (k + 1)) :=
          Summable.tsum_le_tsum hterm hsn (habs.mul_left _)
      _ = X / r₀ * T := tsum_mul_left
  have hlim : Tendsto (fun X : ℝ => X / r₀ * T) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun X : ℝ => X / r₀ * T) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ X in 𝓝[>] (0 : ℝ), ‖a 0‖ ≤ X / r₀ * T := by
    filter_upwards [Ioo_mem_nhdsGT hr₀pos] with X hX
    exact hbound X hX.1 hX.2
  exact norm_le_zero_iff.mp (ge_of_tendsto hlim hev)

/-- A complex power series whose sums vanish at every point of an interval `(0, r)`
has all coefficients zero. -/
theorem eq_zero_of_hasSum_eq_zero {r : ℝ} (hr : 0 < r) :
    ∀ (a : ℕ → ℂ), (∀ X : ℝ, 0 < X → X < r → HasSum (fun k => a k * (X : ℂ) ^ k) 0) →
      ∀ k, a k = 0 := by
  intro a ha k
  induction k generalizing a with
  | zero => exact coeff_zero_eq_zero_of_hasSum_eq_zero hr ha
  | succ k ih =>
    apply ih (fun j => a (j + 1))
    intro X hX hXr
    have h0 := coeff_zero_eq_zero_of_hasSum_eq_zero hr ha
    have hshift := (hasSum_nat_add_iff' 1).mpr (ha X hX hXr)
    simp only [Finset.range_one, Finset.sum_singleton, h0, zero_mul, sub_zero] at hshift
    have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
    have hmul := hshift.mul_left (X : ℂ)⁻¹
    rw [mul_zero] at hmul
    have he : (fun j => a (j + 1) * (X : ℂ) ^ j) =
        fun j => (X : ℂ)⁻¹ * (a (j + 1) * (X : ℂ) ^ (j + 1)) := by
      funext j
      rw [pow_succ]
      field_simp
    rw [he]
    exact hmul

/-- A complex Laurent series with lower-bounded support whose sums vanish at every
point of an interval `(0, r)` has all coefficients zero. -/
theorem eq_zero_of_hasSum_int_eq_zero {c : ℤ → ℂ} {d₀ : ℤ} (hc : ∀ d < d₀, c d = 0)
    {r : ℝ} (hr : 0 < r)
    (hsum : ∀ X : ℝ, 0 < X → X < r → HasSum (fun d : ℤ => c d * (X : ℂ) ^ d) 0)
    (d : ℤ) : c d = 0 := by
  have hinj : Function.Injective (fun k : ℕ => d₀ + (k : ℤ)) := by
    intro k l hkl
    simpa using hkl
  have hnat := eq_zero_of_hasSum_eq_zero hr (fun k => c (d₀ + k)) (by
    intro X hX hXr
    have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
    have h1 := (hinj.hasSum_iff (f := fun d : ℤ => c d * (X : ℂ) ^ d) (fun e he => by
      have hlt : e < d₀ := by
        by_contra hle
        push Not at hle
        exact he ⟨(e - d₀).toNat, by
          change d₀ + ((e - d₀).toNat : ℤ) = e
          rw [Int.toNat_of_nonneg (by omega)]
          ring⟩
      simp only [hc e hlt, zero_mul])).mpr (hsum X hX hXr)
    have h2 := h1.mul_left ((X : ℂ) ^ d₀)⁻¹
    rw [mul_zero] at h2
    have he : (fun k : ℕ => c (d₀ + k) * (X : ℂ) ^ k) =
        fun k : ℕ => ((X : ℂ) ^ d₀)⁻¹ * (((fun d : ℤ => c d * (X : ℂ) ^ d) ∘
          (fun k : ℕ => d₀ + (k : ℤ))) k) := by
      funext k
      simp only [Function.comp_apply, zpow_add₀ hX0, zpow_natCast]
      field_simp
    rw [he]
    exact h2)
  by_cases hd : d < d₀
  · exact hc d hd
  · have hk := hnat (d - d₀).toNat
    have he : d₀ + ((d - d₀).toNat : ℤ) = d := by
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    simpa only [he] using hk

end Laurent

section Strata

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ} {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- Every set of exponents has an open preimage in the quotient. -/
theorem isOpen_quotientExponent_preimage (S : Set (Fin (n + 1) → ℤ)) :
    IsOpen (quotientExponent hϖ ⁻¹' S) := by
  have he : quotientExponent hϖ ⁻¹' S = ⋃ lam ∈ S, sphericalCell hϖ lam := by
    ext t
    simp [sphericalCell]
  rw [he]
  exact isOpen_biUnion (fun lam _ => isOpen_sphericalCell hϖ lam)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The degree-`d` stratum `{t | sphericalQuotientDegree hϖ t = d}` of the quotient. -/
def sphericalDegreeStratum (d : ℤ) : Set (LeftUnipotentQuotient n F) :=
  {t | sphericalQuotientDegree hϖ t = d}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_sphericalDegreeStratum_iff {d : ℤ} {t : LeftUnipotentQuotient n F} :
    t ∈ sphericalDegreeStratum hϖ d ↔ sphericalQuotientDegree hϖ t = d := Iff.rfl

/-- Every degree stratum of the quotient is open. -/
theorem isOpen_sphericalDegreeStratum (d : ℤ) :
    IsOpen (sphericalDegreeStratum (n := n) hϖ d) := by
  have he : sphericalDegreeStratum (n := n) hϖ d =
      quotientExponent hϖ ⁻¹' {lam | ∑ i, lam i = d} := by
    ext t
    simp only [mem_sphericalDegreeStratum_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      sphericalQuotientDegree_eq_sum]
  rw [he]
  exact isOpen_quotientExponent_preimage hϖ _

end Strata

section Bridge

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)

/-- The corank-one integrand at `s` is `q^(-ds)` times the integrand at `0` on the
degree-`d` stratum. -/
theorem corankOneIntegrand_eq_spectralPoint_zpow (W : WhittakerFunctions ψ (n + 1))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) (t : LeftUnipotentQuotient n F) :
    corankOneIntegrand ψ abv W W' s t =
      spectralPoint q s ^ sphericalQuotientDegree h.uniformizer t *
        corankOneIntegrand ψ abv W W' 0 t := by
  induction t using Quotient.inductionOn with
  | h g =>
    rw [corankOneIntegrand_mk, corankOneIntegrand_mk, sphericalQuotientDegree_mk]
    have hq : 0 < q := lt_trans zero_lt_one h.one_lt_q
    have hdet : ((abv (Matrix.det g.val) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (abv.pos (Matrix.GeneralLinearGroup.det_ne_zero g)).ne'
    have hsplit : determinantWeight abv g (s - 1 / 2) =
        determinantWeight abv g s * determinantWeight abv g (0 - 1 / 2) := by
      unfold determinantWeight
      rw [← Complex.cpow_add _ _ hdet]
      congr 1
      ring
    rw [hsplit, determinantWeight_eq_degree_power abv h.uniformizer h.abv_unit q hq
      h.abv_uniformizer g s]
    unfold spectralPoint
    ring

/-- **Analytic bridge.** Where the corank-one integral converges absolutely, it is the
sum over the degrees `d` of `q^(-ds)` times the degree-`d` integral at `s = 0`. -/
theorem hasSum_corankOneIntegral (W : WhittakerFunctions ψ (n + 1))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (hconv : CorankOneConverges ψ abv μ W W' s) :
    HasSum (fun d : ℤ => spectralPoint q s ^ d *
      ∫ t, (if sphericalQuotientDegree h.uniformizer t = d then
        corankOneIntegrand ψ abv W W' 0 t else 0) ∂μ)
      (corankOneIntegral ψ abv μ W W' s) := by
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  let S : ℤ → Set (LeftUnipotentQuotient n F) := sphericalDegreeStratum h.uniformizer
  have hS : ∀ d, MeasurableSet (S d) := fun d =>
    (isOpen_sphericalDegreeStratum h.uniformizer d).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro d e hde
    exact Set.disjoint_left.mpr (fun t h1 h2 => hde (h1.symm.trans h2))
  have hU : ⋃ d, S d = Set.univ :=
    Set.eq_univ_of_forall (fun t => Set.mem_iUnion.mpr ⟨_, rfl⟩)
  have hsum := hasSum_integral_iUnion hS hdisj (by rw [hU]; exact hconv.integrableOn)
  rw [hU, setIntegral_univ] at hsum
  show HasSum _ (∫ t, corankOneIntegrand ψ abv W W' s t ∂μ)
  convert hsum using 1
  funext d
  rw [← integral_indicator (hS d), ← integral_const_mul]
  congr 1
  funext t
  by_cases ht : sphericalQuotientDegree h.uniformizer t = d
  · rw [Set.indicator_of_mem (show t ∈ S d from ht), ite_eq_left ht,
      corankOneIntegrand_eq_spectralPoint_zpow h W W' s t, ht]
  · rw [Set.indicator_of_notMem (show t ∉ S d from ht), ite_eq_right ht, mul_zero]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)
variable (w : (coefficientModel π ℓ).toSubmodule)

/-- If, for every Satake parameter `x`, the corank-one integrals of a smooth model
vector converge and vanish on a real half-line, then every Laurent degree coefficient
vanishes. -/
theorem degreeCorankOneModelCoefficient_eq_zero_of_integrals_eq_zero
    (hzero : ∀ x : Fin (n + 1) → ℂˣ, ∃ a : ℝ, ∀ s : ℝ, a < s →
      CorankOneConverges ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
        corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s = 0)
    (d : ℤ) : degreeCorankOneModelCoefficient h π hπ ℓ w d = 0 := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [map_zero]
  obtain ⟨d₀, hd₀⟩ := degreeCorankOneModelCoefficient_eq_zero_below h π hπ ℓ w
  obtain ⟨a, ha⟩ := hzero x
  have hq1 : (1 : ℝ) < q := by exact_mod_cast h.one_lt_q
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq1
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hcbelow : ∀ e < d₀, symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelCoefficient h π hπ ℓ w e) = 0 := fun e he => by
    rw [hd₀ e he, map_zero]
  refine eq_zero_of_hasSum_int_eq_zero hcbelow (Real.rpow_pos_of_pos hq0 (-a)) ?_ d
  intro X hX hXr
  set s : ℝ := -Real.log X / Real.log q with hsdef
  have hs : a < s := by
    have h1 : Real.log X < Real.log ((q : ℝ) ^ (-a)) := Real.log_lt_log hX hXr
    rw [Real.log_rpow hq0] at h1
    rw [hsdef, lt_div_iff₀ hlogq]
    linarith
  have hrpow : (q : ℝ) ^ (-s) = X := by
    rw [Real.rpow_def_of_pos hq0]
    have hl : Real.log q ≠ 0 := hlogq.ne'
    have hm : Real.log q * -s = Real.log X := by
      rw [hsdef]
      field_simp
    rw [hm, Real.exp_log hX]
  have hXs : spectralPoint q (s : ℂ) = (X : ℂ) := by
    rw [spectralPoint_ofReal, hrpow]
  obtain ⟨hconv, hint⟩ := ha s hs
  have hsum := hasSum_corankOneIntegral h w.val _ (s : ℂ) hconv
  rw [hint, hXs] at hsum
  convert hsum using 1
  funext e
  rw [mul_comm, symmetricTorusEvaluation_degreeCorankOneModelCoefficient]

include hπ in
/-- Under the same hypothesis, a restriction-invariant smooth model vector vanishes
on `diag(GL_(n+1), 1)`. -/
theorem eq_zero_on_restriction_of_integrals_eq_zero
    (hw : IsIntegralInvariantOnRestriction π ℓ w)
    (hzero : ∀ x : Fin (n + 1) → ℂˣ, ∃ a : ℝ, ∀ s : ℝ, a < s →
      CorankOneConverges ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
        corankOneIntegral ψ abv μ w.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s = 0)
    (g : Langlands.GeneralLinear (n + 1) F) :
    w.val.val (rankInclusion 1 g) = 0 :=
  eq_zero_on_restriction_of_degreeCoefficients_eq_zero h π hπ ℓ w hw
    (degreeCorankOneModelCoefficient_eq_zero_of_integrals_eq_zero h π hπ ℓ w hzero) g

end Bridge

section Essential

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π)

/-- The corank-one integrals of the difference of two essential vectors converge and
vanish on a real half-line, for every Satake parameter. -/
theorem IsEssentialVector.sub_integrals_eq_zero {w₁ w₂ : (coefficientModel π ℓ).toSubmodule}
    (h₁ : IsEssentialVector h π ℓ w₁) (h₂ : IsEssentialVector h π ℓ w₂)
    (x : Fin (n + 1) → ℂˣ) :
    ∃ a : ℝ, ∀ s : ℝ, a < s →
      CorankOneConverges ψ abv μ (w₁ - w₂).val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
        corankOneIntegral ψ abv μ (w₁ - w₂).val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s = 0 := by
  obtain ⟨⟨P, hP, hid₁⟩, -⟩ := h₁
  have hid₂ := IsEssentialVector.satisfiesEssentialIdentity h π ℓ h₂ hP
  obtain ⟨⟨a₁, hc₁⟩, ⟨b₁, hr₁⟩⟩ := hid₁ x
  obtain ⟨⟨a₂, hc₂⟩, ⟨b₂, hr₂⟩⟩ := hid₂ x
  refine ⟨max (max a₁ a₂) (max b₁ b₂), fun s hs => ?_⟩
  have hre : ((s : ℂ)).re = s := Complex.ofReal_re s
  have ha₁ : a₁ < ((s : ℂ)).re := by
    rw [hre]; exact lt_of_le_of_lt (le_max_of_le_left (le_max_left _ _)) hs
  have ha₂ : a₂ < ((s : ℂ)).re := by
    rw [hre]; exact lt_of_le_of_lt (le_max_of_le_left (le_max_right _ _)) hs
  have hb₁ : b₁ < ((s : ℂ)).re := by
    rw [hre]; exact lt_of_le_of_lt (le_max_of_le_right (le_max_left _ _)) hs
  have hb₂ : b₂ < ((s : ℂ)).re := by
    rw [hre]; exact lt_of_le_of_lt (le_max_of_le_right (le_max_right _ _)) hs
  have hcv₁ := hc₁ s ha₁
  have hcv₂ := hc₂ s ha₂
  rw [Submodule.coe_sub]
  refine ⟨CorankOneConverges.sub ψ abv μ hcv₁ hcv₂, ?_⟩
  rw [corankOneIntegral_sub ψ abv μ hcv₁ hcv₂, (hr₁ s hb₁).2, (hr₂ s hb₂).2, sub_self]

/-- **Two essential vectors agree on `diag(GL_(n+1), 1)`.** -/
theorem IsEssentialVector.eq_on_restriction (hπ : IsSmooth π)
    {w₁ w₂ : (coefficientModel π ℓ).toSubmodule}
    (h₁ : IsEssentialVector h π ℓ w₁) (h₂ : IsEssentialVector h π ℓ w₂)
    (g : Langlands.GeneralLinear (n + 1) F) :
    w₁.val.val (rankInclusion 1 g) = w₂.val.val (rankInclusion 1 g) := by
  have hw : IsIntegralInvariantOnRestriction π ℓ (w₁ - w₂) := by
    intro g' k
    have e₁ := h₁.2 g' k
    have e₂ := h₂.2 g' k
    change w₁.val.val _ - w₂.val.val _ = w₁.val.val _ - w₂.val.val _
    rw [e₁, e₂]
  have hz := eq_zero_on_restriction_of_integrals_eq_zero h π hπ ℓ (w₁ - w₂) hw
    (IsEssentialVector.sub_integrals_eq_zero h π ℓ h₁ h₂) g
  change w₁.val.val _ - w₂.val.val _ = 0 at hz
  exact sub_eq_zero.mp hz

/-- **Two essential vectors agree on the mirabolic subgroup** of `GL_(n+2)`. -/
theorem IsEssentialVector.eq_on_mirabolic (hπ : IsSmooth π)
    {w₁ w₂ : (coefficientModel π ℓ).toSubmodule}
    (h₁ : IsEssentialVector h π ℓ w₁) (h₂ : IsEssentialVector h π ℓ w₂)
    (p : mirabolic (n + 1) F) :
    w₁.val.val p.val = w₂.val.val p.val :=
  whittaker_mirabolic_eq_of_levi_eq ψ w₁.val w₂.val
    (IsEssentialVector.eq_on_restriction h π ℓ hπ h₁ h₂) p

end Essential

end Langlands.Conductor
