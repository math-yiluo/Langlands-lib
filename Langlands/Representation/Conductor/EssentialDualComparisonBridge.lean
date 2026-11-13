import Langlands.Representation.Conductor.EssentialDualComparisonReduction
import Langlands.Representation.Conductor.EssentialDualComparisonStatement
import Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationStatement
import Langlands.Representation.Conductor.EssentialConductorAssembly
import Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityStatement
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialDualIntegral

/-!
# The dual comparison of essential vectors from the spherical functional equation

The corank-one functional equation against unitary spherical functions
(`SphericalCorankOneFunctionalEquationStatement`), applied to the vector of the essential
vector `w` of `π` at the parameter `x⁻¹`, makes the dual integral of `W̃` against
`W(·; x; ψ)` equal to `c^(n+1) (∏ xᵢ)^(-m) q^(-N) X^(-N) / ∏ P̃(xᵢ X)`, `N = (n + 1) m`,
`X = q^(-s)`. The right translate `W₁` of the essential vector of the dual model by
`diag(ϖ^m, ..., ϖ^m, 1)` has integral `(∏ xᵢ)^(-m) q^(-N/2) X^(-N) / ∏ P̃(xᵢ X)`. So the
two integrals are proportional with the constant `c^(n+1) q^(-N/2)`, independent of `x`
and `s`; with mirabolic restriction injectivity this gives JPSS 1981 (5.3).
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial QuotientIntegration
open Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical

universe uF uV

/-! ### Elementary facts about rational functions and spectral points -/

/-- A nonzero polynomial has no roots of large absolute value. -/
theorem exists_eval_ne_zero_of_lt_norm {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ B : ℝ, ∀ t : ℂ, B < ‖t‖ → p.eval t ≠ 0 := by
  classical
  refine ⟨∑ r ∈ p.roots.toFinset, ‖r‖, fun t ht h0 => ?_⟩
  have hr : t ∈ p.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr h0)
  have hle := Finset.single_le_sum (f := fun r : ℂ => ‖r‖) (fun r _ => norm_nonneg r) hr
  linarith

/-- `q^(s - 1)` exceeds `B` once `s > ⌈B⌉ + 1`. -/
theorem lt_rpow_sub_one_of_ceil_lt {q : ℕ} (hq : 1 < q) {B s : ℝ}
    (hs : (⌈B⌉₊ : ℝ) + 1 < s) : B < (q : ℝ) ^ (s - 1) := by
  set k := ⌈B⌉₊
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : B ≤ k := Nat.le_ceil B
  have h2 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self
  have h3 : (2 : ℝ) ^ k ≤ (q : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hq2 k
  have h4 : (q : ℝ) ^ k ≤ (q : ℝ) ^ (s - 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  linarith

/-- For real `s`, `|q^(-(1-s))| = q^(s - 1)`. -/
theorem norm_spectralPoint_one_sub_ofReal (q : ℕ) (s : ℝ) :
    ‖spectralPoint q (1 - (s : ℂ))‖ = (q : ℝ) ^ (s - 1) := by
  have he : (1 - (s : ℂ)) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  rw [he, spectralPoint_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _), neg_sub]

/-- If `R = p⁻¹` and `R` has no pole at `t`, then `R(t) p(t) = 1`. -/
theorem eval_mul_eval_eq_one_of_eq_inv {R : RatFunc ℂ} {p : ℂ[X]}
    (hR : R = (algebraMap ℂ[X] (RatFunc ℂ) p)⁻¹) (hp : p ≠ 0) {t : ℂ}
    (ht : R.denom.eval t ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) t R * p.eval t = 1 := by
  have hp' : algebraMap ℂ[X] (RatFunc ℂ) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).mpr hp
  have h1 : R * algebraMap ℂ[X] (RatFunc ℂ) p = 1 := by
    rw [hR, inv_mul_cancel₀ hp']
  have h2 := congrArg (RatFunc.eval (RingHom.id ℂ) t) h1
  rwa [RatFunc.eval_mul (RingHom.id ℂ) t ht (by simp [RatFunc.denom_algebraMap]),
    RatFunc.eval_algebraMap,
    RatFunc.eval_one, Polynomial.eval₂_id] at h2

/-- The polynomial `∏ i, P(x_i X)` of a polynomial with constant term one is nonzero. -/
theorem prod_comp_ne_zero {m : ℕ} {P : ℂ[X]} (hP : P.coeff 0 = 1) (x : Fin m → ℂˣ) :
    (∏ i, P.comp (C (x i : ℂ) * X)) ≠ 0 := by
  intro h0
  apply essentialFactor_ne_zero hP x
  rw [essentialFactor_eq, h0, map_zero, inv_zero]

/-! ### Central translation of the spherical function and of corank-one integrals -/

section Translation

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] {n : ℕ}

/-- The spherical function transforms under the central element `ϖ^t` by `(∏ xᵢ)^t`. -/
theorem inverseSphericalWhittaker_mul_scalar {ψ : UnitaryAdditiveCharacter F}
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1) {ϖ : Fˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (q : ℕ)
    (x : Fin (n + 1) → ℂˣ) (g : Langlands.GeneralLinear (n + 1) F) (t : ℤ) :
    (inverseSphericalWhittaker hψ hϖ q x).val (g * scalar (ϖ ^ t)) =
      ((∏ i, x i : ℂˣ) : ℂ) ^ t * (inverseSphericalWhittaker hψ hϖ q x).val g := by
  rw [inverseSphericalWhittaker_apply, inverseSphericalWhittaker_apply]
  change sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q x
      (g * torus ϖ (fun _ : Fin (n + 1) => t)) = _
  rw [← symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    ← symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    sphericalWhittakerPolynomial_mul_torus_const hϖ _ q
      (isIntegrallyTrivial_inverseStandardCharacter hψ n), map_mul,
    algHom_apply_unit_zpow, symmetricTorusEvaluation_determinantUnit,
    Units.val_zpow_eq_zpow_val]

/-- Right translation by `diag(a, 1)` against a function `X` with `X(g a⁻¹) = κ X(g)`
multiplies the corank-one integrand by `κ |det a⁻¹|^(s - 1/2)` after the substitution
`g ↦ g a`. -/
theorem corankOneIntegrand_rankInclusion_translate [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (W W₁ : WhittakerFunctions ψ (n + 1))
    (X : InverseWhittakerFunctions ψ n) (a : Langlands.GeneralLinear (n + 1) F) (κ : ℂ)
    (hW : ∀ g, W₁.val (rankInclusion 1 g) = W.val (rankInclusion 1 (g * a)))
    (hX : ∀ g, X.val (g * a⁻¹) = κ * X.val g) (s : ℂ) :
    corankOneIntegrand ψ abv W₁ X s = fun y => (κ * determinantWeight abv a⁻¹ (s - 1 / 2)) *
      corankOneIntegrand ψ abv W X s (rightTranslate (upperUnipotent (n + 1) F) a y) := by
  funext y
  induction y using Quotient.inductionOn with
  | h g =>
    rw [rightTranslate_mk, corankOneIntegrand_mk, corankOneIntegrand_mk, hW]
    have hXg : X.val g = κ * X.val (g * a) := by rw [← hX, mul_inv_cancel_right]
    have hd : determinantWeight abv g (s - 1 / 2) =
        determinantWeight abv (g * a) (s - 1 / 2) * determinantWeight abv a⁻¹ (s - 1 / 2) := by
      rw [← determinantWeight_mul, mul_inv_cancel_right]
    rw [hXg, hd]
    ring

/-- Convergence and value of the corank-one integral of a right translate by `diag(a, 1)`. -/
theorem corankOne_rankInclusion_translate [IsNonarchimedeanLocalField F]
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {μ : Measure (LeftUnipotentQuotient n F)}
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (W W₁ : WhittakerFunctions ψ (n + 1))
    (X : InverseWhittakerFunctions ψ n) (a : Langlands.GeneralLinear (n + 1) F) (κ : ℂ)
    (hW : ∀ g, W₁.val (rankInclusion 1 g) = W.val (rankInclusion 1 (g * a)))
    (hX : ∀ g, X.val (g * a⁻¹) = κ * X.val g) (s : ℂ) :
    (CorankOneConverges ψ abv μ W X s → CorankOneConverges ψ abv μ W₁ X s) ∧
      corankOneIntegral ψ abv μ W₁ X s =
        (κ * determinantWeight abv a⁻¹ (s - 1 / 2)) * corankOneIntegral ψ abv μ W X s := by
  have he := corankOneIntegrand_rankInclusion_translate ψ abv W W₁ X a κ hW hX s
  have hmp := hμ.right_invariant a
  have hemb := (rightTranslate (upperUnipotent (n + 1) F) a).measurableEmbedding
  refine ⟨fun hint => ?_, ?_⟩
  · unfold CorankOneConverges
    rw [he]
    exact ((hmp.integrable_comp_emb hemb).mpr hint).const_mul _
  · unfold corankOneIntegral
    rw [he, integral_const_mul, hmp.integral_comp hemb (corankOneIntegrand ψ abv W X s)]

end Translation

/-! ### The proportionality of the spherical integrals -/

/-- The constant `C' = c^(n+1) q^(-N) (q^(-N/2))⁻¹ = c^(n+1) q^(-N/2)`, `N = (n + 1) m`, of
JPSS 1981 (5.3): the dual of the essential vector is `C'` times the translate of the
essential vector of the dual model by `diag(ϖ^m, ..., ϖ^m, 1)`. -/
def essentialDualConstant (q n : ℕ) (c : ℂˣ) (m : ℤ) : ℂ :=
  (c : ℂ) ^ (n + 1) * (q : ℂ) ^ (-(((n + 1 : ℕ) : ℤ) * m)) *
    ((q : ℂ) ^ (-((((n + 1 : ℕ) : ℤ) * m : ℤ) : ℂ) / 2))⁻¹

section Proportional

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]

omit [T2Space F] [TotallyDisconnectedSpace F] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)] in
/-- `|det (diag(ϖ^m, ..., ϖ^m))⁻¹| = q^((n + 1) m)` for Jacquet's normalized absolute
value. -/
theorem abv_det_scalar_zpow_inv {q : ℕ} {ψ : UnitaryAdditiveCharacter F}
    {abv : AbsoluteValue F ℝ} {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
    (h : IsJacquetNormalization q ψ abv ϖ μ) (m : ℤ) :
    abv (Matrix.det ((scalar (n := n + 1) (ϖ ^ m))⁻¹ :
        Langlands.GeneralLinear (n + 1) F).val) =
      (q : ℝ) ^ (((n + 1 : ℕ) : ℤ) * m) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (h.one_lt_q.trans' Nat.zero_lt_one).ne'
  have hdet : Matrix.det ((scalar (n := n + 1) (ϖ ^ m))⁻¹ :
      Langlands.GeneralLinear (n + 1) F).val = (ϖ : F) ^ (-(((n + 1 : ℕ) : ℤ) * m)) := by
    rw [← map_inv, ← zpow_neg]
    change ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (ϖ ^ (-m))) : Fˣ) : F) = _
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← zpow_natCast, ← zpow_mul,
      Units.val_zpow_eq_zpow_val]
    congr 1
    push_cast
    ring
  rw [hdet, map_zpow₀, h.abv_uniformizer, inv_zpow', neg_neg]

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}

set_option maxHeartbeats 1000000 in
/-- The functional equation and the two essential identities make the dual integral of the
essential vector of `π` equal to `essentialDualConstant q n c m` times the integral of the
translated essential vector of the dual model, against every unitary spherical function. -/
theorem dualSpherical_proportional
    (hFE : SphericalCorankOneFunctionalEquationStatement.{uF, uV})
    (h : IsJacquetNormalization q ψ abv ϖ μ)
    (h' : IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ)
    {ν : AdditiveHaarMeasure F} (hν : IsSelfDual ψ ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
    (hπ : IsGeneric ψ (n + 1) π) (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0)
    (w : (coefficientModel π ℓ).toSubmodule) (hw : IsEssentialVector h π ℓ w)
    (ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) (inverseTransposePullback π))
    (hℓ' : ℓ'.val = (dualFunctional ψ π ℓ).val)
    (w' : (coefficientModel (inverseTransposePullback π) ℓ').toSubmodule)
    (hw' : IsEssentialVector h' (inverseTransposePullback π) ℓ' w')
    (c : ℂˣ) (m : ℤ) (hε : IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, m)) :
    ∀ x : Fin (n + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) →
      ∃ a : ℝ, ∀ s : ℝ, a < s →
        CorankOneConverges (ψ.scale (-1)) abv μ
          (dualComparisonModelMap π ℓ ℓ' hℓ' w).val
          (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x) s ∧
        CorankOneConverges (ψ.scale (-1)) abv μ
          (modelRepresentation (inverseTransposePullback π) ℓ'
            (rankInclusion 1 (scalar (ϖ ^ m))) w').val
          (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x) s ∧
        corankOneIntegral (ψ.scale (-1)) abv μ
          (dualComparisonModelMap π ℓ ℓ' hℓ' w).val
          (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x) s =
          essentialDualConstant q n c m * corankOneIntegral (ψ.scale (-1)) abv μ
            (modelRepresentation (inverseTransposePullback π) ℓ'
              (rankInclusion 1 (scalar (ϖ ^ m))) w').val
            (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x) s := by
  have hq := h.one_lt_q
  have hq0 : 0 < q := by omega
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have := h'.borel
  obtain ⟨⟨P, hP, hidP⟩, -⟩ := hw
  obtain ⟨⟨Pd, hPd, hidPd⟩, -⟩ := hw'
  obtain ⟨v, hv⟩ := w.property
  rw [essentialDualConstant]
  set N : ℤ := ((n + 1 : ℕ) : ℤ) * m with hN
  intro x hx
  set Y := inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x with hY
  -- The dual function of `w` is the coefficient of `v` for `ℓ'`.
  have hWd : (dualComparisonModelMap π ℓ ℓ' hℓ' w).val =
      coefficientMap (inverseTransposePullback π) ℓ' v := by
    apply Subtype.ext
    funext g
    rw [dualComparisonModelMap_apply, dualFunction_apply, ← hv]
    change ℓ.val (π (weylLong ((n + 1) + 1) F * inverseTranspose ((n + 1) + 1) F g) v) =
      ℓ'.val (π (inverseTranspose ((n + 1) + 1) F g) v)
    rw [hℓ', map_mul, Module.End.mul_apply]
    rfl
  -- The functional equation at `x⁻¹`.
  have hxi : ∀ i, ‖((x⁻¹ i : ℂˣ) : ℂ)‖ = 1 := fun i => by
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hx i, inv_one]
  obtain ⟨-, ⟨ad, had⟩, R, Rd, hR, hRd, hNFE⟩ :=
    hFE F n q ψ abv ϖ μ h h' ν hν π hπ ℓ hℓ ℓ' hℓ' c m hε P Pd hP hPd v x⁻¹ hxi
  rw [inv_inv] at had hRd hNFE
  -- The forward continuation is the essential factor.
  have hR' : R = essentialFactor P x⁻¹ := by
    have he := (hidP x⁻¹).2
    rw [← hv] at he
    exact HasRationalContinuation.unique hq hR he
  rw [essentialFactor_eq] at hR'
  have hPp := prod_comp_ne_zero hP.1 x⁻¹
  -- The essential identity of `w'` at `x`.
  obtain ⟨⟨ae, hae⟩, hRe⟩ := hidPd x
  have hRe' := hRe
  obtain ⟨ae', hae'⟩ := hRe
  have hPe := prod_comp_ne_zero hPd.1 x
  obtain ⟨ad', had'⟩ := hRd
  obtain ⟨B, hB⟩ := exists_eval_ne_zero_of_lt_norm (RatFunc.denom_ne_zero R)
  -- The translate.
  set a : Langlands.GeneralLinear (n + 1) F := scalar (n := n + 1) (ϖ ^ m) with ha
  set κ : ℂ := ((∏ i, x i : ℂˣ) : ℂ) ^ (-m) with hκ
  have hXa : ∀ g, Y.val (g * a⁻¹) = κ * Y.val g := fun g => by
    rw [ha, ← map_inv, ← zpow_neg, hY, inverseSphericalWhittaker_mul_scalar]
  have hWa : ∀ g, ((modelRepresentation (inverseTransposePullback π) ℓ'
      (rankInclusion 1 (scalar (ϖ ^ m))) w').val).val (rankInclusion 1 g) =
      w'.val.val (rankInclusion 1 (g * a)) := fun g => by
    change w'.val.val (rankInclusion 1 g * rankInclusion 1 (scalar (ϖ ^ m))) = _
    rw [← map_mul]
  refine ⟨max (max ad ad') (max (max ae ae') ((⌈B⌉₊ : ℝ) + 1)), fun s hs => ?_⟩
  have hs1 : ad < s := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs2 : ad' < s := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs3 : ae < s := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hs
  have hs4 : ae' < s := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hs
  have hs5 : (⌈B⌉₊ : ℝ) + 1 < s := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hre : ((s : ℂ)).re = s := Complex.ofReal_re s
  obtain ⟨htrans, hval⟩ := corankOne_rankInclusion_translate (ψ.scale (-1)) abv h'.measure
    w'.val ((modelRepresentation (inverseTransposePullback π) ℓ'
      (rankInclusion 1 (scalar (ϖ ^ m))) w').val) Y a κ hWa hXa s
  refine ⟨?_, htrans (hae s (by rw [hre]; exact hs3)), ?_⟩
  · rw [hWd]
    exact had s (by rw [hre]; exact hs1)
  -- Values at `s`.
  set Xs := spectralPoint q (s : ℂ) with hXs
  have hXs0 : Xs ≠ 0 := spectralPoint_ne_zero_of_pos hq0 _
  obtain ⟨hRdden, hJ⟩ := had' s (by rw [hre]; exact hs2)
  obtain ⟨hEden, hE⟩ := hae' s (by rw [hre]; exact hs4)
  -- The forward continuation has no pole at `1 - s`.
  have hRden : R.denom.eval (spectralPoint q (1 - (s : ℂ))) ≠ 0 := by
    apply hB
    rw [norm_spectralPoint_one_sub_ofReal]
    exact lt_rpow_sub_one_of_ceil_lt hq hs5
  have hFEs := hNFE (1 - (s : ℂ)) hRden (by rw [sub_sub_cancel]; exact hRdden)
  rw [sub_sub_cancel, pow_zero, one_mul] at hFEs
  have hRone := eval_mul_eval_eq_one_of_eq_inv hR' hPp hRden
  have hEone := eval_mul_eval_eq_one_of_eq_inv (essentialFactor_eq Pd x) hPe hEden
  -- Evaluate the epsilon monomial.
  have hprod : (∏ i, x⁻¹ i) = (∏ i, x i)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    rfl
  have hxinv : ((c ^ (n + 1) * (∏ i, x⁻¹ i) ^ m : ℂˣ) : ℂ) = (c : ℂ) ^ (n + 1) * κ := by
    simp only [hκ, hprod, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      inv_zpow']
  have hsp1 : spectralPoint q (1 - (s : ℂ)) ^ N = (q : ℂ) ^ (-N) * Xs ^ (-N) := by
    rw [HighlyRamified.spectralPoint_one_sub q hq0, mul_zpow, inv_zpow', inv_zpow']
  have hdet : determinantWeight abv a⁻¹ ((s : ℂ) - 1 / 2) =
      (q : ℂ) ^ (-(N : ℂ) / 2) * Xs ^ (-N) := by
    unfold determinantWeight
    rw [abv_det_scalar_zpow_inv h' m]
    exact HighlyRamified.ofReal_zpow_cpow_eq hq0 N s
  unfold epsilonMonomial at hFEs
  rw [hxinv, hsp1, mul_comm (eval _ _) (RatFunc.eval _ _ R), hRone, mul_one] at hFEs
  -- Assemble.
  set Pe := ∏ i, Pd.comp (C (x i : ℂ) * X) with hPedef
  have hPeval : Pe.eval Xs ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hEone
    exact zero_ne_one hEone
  rw [hWd, hJ, hval, hE, hdet]
  have hq2 : (q : ℂ) ^ (-(N : ℂ) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h0 => hqC h0.1
  apply mul_left_cancel₀ hPeval
  rw [hFEs]
  have hE' : RatFunc.eval (RingHom.id ℂ) Xs
      (essentialFactor Pd x) = (Pe.eval Xs)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left hEone
  rw [hE']
  generalize (q : ℂ) ^ (-(N : ℂ) / 2) = Z at hq2 ⊢
  field_simp

end Proportional

/-- JPSS 1981 (5.3) from the spherical corank-one functional equation and mirabolic
restriction injectivity. -/
theorem essentialDualComparison_of_functionalEquation
    (hFE : SphericalCorankOneFunctionalEquationStatement.{uF, uV})
    (hinj : MirabolicRestrictionInjectivityStatement.{uF, uV}) :
    EssentialDualComparisonStatement.{uF, uV} := by
  intro F _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ q ψ abv ϖ μ h h' ν hν V _ _ π hπ ℓ hℓ
    w hw ℓ' hℓ' w' hw' c m hε
  have hℓ'0 : ℓ'.val ≠ 0 := by
    rw [hℓ']
    exact dualFunctional_nonzero ψ π ℓ hℓ
  exact dualComparison_of_unit_spherical_integrals h' π ℓ hπ.2.1.1
    (hinj F (n + 1) ψ π hπ ℓ hℓ) w hw.2 ℓ' hℓ'
    (hinj F (n + 1) (ψ.scale (-1)) (inverseTransposePullback π)
      (isGeneric_inverseTransposePullback ψ π hπ) ℓ' hℓ'0) w' hw'.2 m
    ⟨essentialDualConstant q n c m,
      dualSpherical_proportional hFE h h' hν π hπ ℓ hℓ w hw ℓ' hℓ' w' hw' c m hε⟩

end Langlands.Conductor
