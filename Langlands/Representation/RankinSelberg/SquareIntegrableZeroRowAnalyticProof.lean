import Langlands.Representation.RankinSelberg.SquareIntegrableZeroRowAnalyticStatement
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionStatement
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionProof
import Langlands.Representation.RankinSelberg.WeightedWhittakerSquareStatement
import Langlands.Representation.RankinSelberg.WeightedWhittakerSquareProof
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowIntegrandContinuityProof
import Langlands.Analysis.MellinHalfPlaneProof
import Langlands.Analysis.Local.QuotientTopology
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Prod

/-! Sharp zero-row convergence and holomorphy from the two Whittaker square estimates. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]

private def zeroRowProductEquiv (n : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)] :
    (LeftUnipotentQuotient n F × Matrix (Fin 0) (Fin (n + 1)) F) ≃ᵐ
      LeftUnipotentQuotient n F where
  toFun := Prod.fst
  invFun := fun q => (q, 0)
  left_inv := by intro q; exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv := by intro q; rfl
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_id.prodMk measurable_const

private theorem zeroRow_integrable_iff {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (f : LeftUnipotentQuotient n F → ℂ) :
    Integrable (fun qx : LeftUnipotentQuotient n F × Matrix (Fin 0) (Fin (n + 1)) F =>
      f qx.1) (μ.prod (rectangularMeasure ν 0 (n + 1))) ↔ Integrable f μ := by
  rw [rectangularMeasure_zero_rows]
  exact measurePreserving_fst.integrable_comp_emb (zeroRowProductEquiv n).measurableEmbedding

private theorem zeroRow_converges_iff (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    UnequalRankConverges ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' s ↔
      Integrable (unequalRankIntegrand ψ abv 0 k W W' s 0) μ := by
  unfold UnequalRankConverges
  have h : (fun qx : LeftUnipotentQuotient n F × Matrix (Fin 0) (Fin (n + 1)) F =>
      unequalRankIntegrand ψ abv 0 k W W' s qx.2 qx.1) =
      fun qx => unequalRankIntegrand ψ abv 0 k W W' s 0 qx.1 := by
    funext qx
    rw [Subsingleton.elim qx.2 (0 : Matrix (Fin 0) (Fin (n + 1)) F)]
  rw [h]
  exact zeroRow_integrable_iff μ ν _

private theorem zeroRow_integral (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' s =
      ∫ q, unequalRankIntegrand ψ abv 0 k W W' s 0 q ∂μ := by
  simp [unequalRankIntegral]

omit [MeasurableSpace F] in
private theorem zeroRow_integrand_of_zero (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (h : W = 0 ∨ W' = 0)
    (s : ℂ) (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv 0 k W W' s 0 q = 0 := by
  induction q using Quotient.inductionOn with
  | h g =>
    rcases h with h | h
    · subst W
      simp [unequalRankIntegrand_mk]
    · subst W'
      simp [unequalRankIntegrand_mk]

private theorem zeroRow_analytic_of_zero (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (h : W = 0 ∨ W' = 0) :
    (∀ s : ℂ, UnequalRankConverges ψ abv 0 k μ
      (rectangularMeasure ν 0 (n + 1)) W W' s) ∧
    Differentiable ℂ (unequalRankIntegral ψ abv 0 k μ
      (rectangularMeasure ν 0 (n + 1)) W W') := by
  have hz (s : ℂ) :
      unequalRankIntegrand ψ abv 0 k W W' s 0 = fun _ => 0 := by
    funext q
    exact zeroRow_integrand_of_zero ψ abv k W W' h s q
  constructor
  · intro s
    rw [zeroRow_converges_iff, hz]
    exact integrable_zero _ _ _
  · have hi : unequalRankIntegral ψ abv 0 k μ
        (rectangularMeasure ν 0 (n + 1)) W W' = fun _ => 0 := by
      funext s
      rw [zeroRow_integral, hz]
      simp
    rw [hi]
    exact differentiable_const _

private theorem coefficientModel_zero_value
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    {N : Subgroup G} {θ : N →* ℂˣ} (π : Representation ℂ G V)
    (ℓ : functionals N θ π) (hℓ : ℓ = 0)
    (f : (coefficientModel π ℓ).toSubmodule) : f.val = 0 := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  apply Subtype.ext
  funext g
  change ℓ.val (π g v) = 0
  simp [hℓ]

private theorem integrable_of_two_square_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (a b : X → ℝ) (hf : AEStronglyMeasurable f μ)
    (ha : Integrable (fun x => a x ^ 2) μ)
    (hb : Integrable (fun x => b x ^ 2) μ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ a x * b x) :
    Integrable f μ := by
  apply ((ha.add hb).div_const 2).mono' hf
  filter_upwards [hbound] with x hx
  change ‖f x‖ ≤ (a x ^ 2 + b x ^ 2) / 2
  nlinarith [sq_nonneg (a x - b x)]

omit [MeasurableSpace F] in
private theorem norm_zeroRow_integrand_mk (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    ‖unequalRankIntegrand ψ abv 0 k W W' s 0 (Quotient.mk _ g)‖ =
      ‖W.val (appendIdentity n (0 + k + 1) g)‖ * ‖W'.val g‖ *
        (abv (Matrix.det g.val)) ^ (s.re - ((0 + k + 1 : ℕ) : ℝ) / 2) := by
  rw [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows, norm_mul, norm_mul]
  unfold determinantWeight
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (abv.pos g.det_ne_zero)]
  simp

private theorem integrable_mellin_of_weighted_squares
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : X → ℂ) (u v d : X → ℝ) (r : ℝ) (s : ℂ)
    (hd : ∀ x, 0 < d x) (hc : ∀ x, ‖c x‖ = u x * v x)
    (hf : AEStronglyMeasurable
      (fun x => c x * (d x : ℂ) ^ (s - (r / 2 : ℝ))) μ)
    (hu : Integrable (fun x => u x ^ 2 * d x ^ (-r)) μ)
    (hv : Integrable (fun x => v x ^ 2 * d x ^ (2 * s.re)) μ) :
    Integrable (fun x => c x * (d x : ℂ) ^ (s - (r / 2 : ℝ))) μ := by
  apply integrable_of_two_square_bounds μ _ (fun x => u x * d x ^ (-r / 2))
    (fun x => v x * d x ^ s.re) hf
  · convert hu using 1
    funext x
    rw [mul_pow, ← Real.rpow_mul_natCast (hd x).le]
    congr 2
    ring
  · convert hv using 1
    funext x
    rw [mul_pow, ← Real.rpow_mul_natCast (hd x).le]
    congr 2
    ring
  · apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul, hc, Complex.norm_cpow_eq_rpow_re_of_pos (hd x)]
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [show s.re - r / 2 = -r / 2 + s.re by ring, Real.rpow_add (hd x)]
    exact le_of_eq (by ring)

omit [MeasurableSpace F] in
private theorem zeroRow_integrand_mellin (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv 0 k W W' s 0 q =
      unequalRankIntegrand ψ abv 0 k W W'
        (((0 + k + 1 : ℕ) : ℝ) / 2 : ℝ) 0 q *
        (quotientDeterminantAbs abv n q : ℂ) ^
          (s - ((((0 + k + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ)) := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows, determinantWeight]

omit [MeasurableSpace F] in
private theorem quotientDeterminantAbs_continuous
    [IsTopologicalRing F] (abv : AbsoluteValue F ℝ)
    (habv : Continuous abv) (n : ℕ) :
    Continuous (quotientDeterminantAbs abv n) := by
  apply (QuotientIntegration.leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  exact habv.comp Units.continuous_val.matrix_det

omit [MeasurableSpace F] in
private theorem zeroRow_coefficient_norm_of_cutoff
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hcut : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (appendIdentity n (0 + k + 1) g) * Φ (lastRow g) =
        W.val (appendIdentity n (0 + k + 1) g))
    (q : LeftUnipotentQuotient n F) :
    ‖unequalRankIntegrand ψ abv 0 k W W'
        (((0 + k + 1 : ℕ) : ℝ) / 2 : ℝ) 0 q‖ =
      restrictedWhittakerNorm ψ k W q *
        (inverseWhittakerNorm ψ W' q * ‖Φ (quotientLastRow n q)‖) := by
  induction q using Quotient.inductionOn with
  | h g =>
    have hnorm := congrArg norm (hcut g)
    rw [norm_mul] at hnorm
    rw [norm_zeroRow_integrand_mk]
    simp only [Complex.ofReal_re, sub_self, Real.rpow_zero, mul_one,
      restrictedWhittakerNorm_mk, inverseWhittakerNorm_mk, quotientLastRow_mk]
    calc
      _ = (‖W.val (appendIdentity n (0 + k + 1) g)‖ *
          ‖Φ (lastRow g)‖) * ‖W'.val g‖ := by rw [hnorm]
      _ = _ := by ring

private theorem zeroRow_analytic_of_square_estimates
    [IsTopologicalRing F]
    (hM : Langlands.Analysis.MellinHalfPlaneStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (habv : Continuous abv) {n : ℕ} (k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [BorelSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    {V V' : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (hπ : IsSmooth π) (hσ : IsSmooth σ)
    (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
    (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hcut : ∀ g : Langlands.GeneralLinear (n + 1) F,
      f.val.val (appendIdentity n (0 + k + 1) g) * Φ (lastRow g) =
        f.val.val (appendIdentity n (0 + k + 1) g))
    (hrestriction : Integrable
      (fun q => restrictedWhittakerNorm ψ k f.val q ^ 2 *
        quotientDeterminantAbs abv n q ^ (-((0 + k + 1 : ℕ) : ℝ))) μ)
    (hweighted : ∀ a : ℝ, 0 < a → Integrable
      (fun q => inverseWhittakerNorm ψ f'.val q ^ 2 *
        ‖Φ (quotientLastRow n q)‖ ^ 2 *
        quotientDeterminantAbs abv n q ^ (2 * a)) μ) :
    (∀ s : ℂ, 0 < s.re →
      UnequalRankConverges ψ abv 0 k μ
        (rectangularMeasure ν 0 (n + 1)) f.val f'.val s) ∧
    DifferentiableOn ℂ
      (unequalRankModelIntegral ψ abv 0 k μ
        (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f')
      {s : ℂ | 0 < s.re} := by
  let r : ℝ := ((0 + k + 1 : ℕ) : ℝ)
  let c := unequalRankIntegrand ψ abv 0 k f.val f'.val (r / 2 : ℝ) 0
  let d := quotientDeterminantAbs abv n
  let u := restrictedWhittakerNorm ψ k f.val
  let v := fun q => inverseWhittakerNorm ψ f'.val q * ‖Φ (quotientLastRow n q)‖
  have hd : ∀ q, 0 < d q := quotientDeterminantAbs_pos abv n
  have hc : ∀ q, ‖c q‖ = u q * v q :=
    zeroRow_coefficient_norm_of_cutoff ψ abv k f.val f'.val Φ hcut
  have hfactor (s : ℂ) (q : LeftUnipotentQuotient n F) :
      unequalRankIntegrand ψ abv 0 k f.val f'.val s 0 q =
        c q * (d q : ℂ) ^ (s - (r / 2 : ℝ)) :=
    zeroRow_integrand_mellin ψ abv k f.val f'.val s q
  have hmeas (s : ℂ) :
      AEStronglyMeasurable (fun q => c q * (d q : ℂ) ^ (s - (r / 2 : ℝ))) μ := by
    convert (unequalRankZeroRowIntegrandContinuous F n k abv habv V V' π σ hπ hσ ψ
      ℓ ℓ' f f' s).aestronglyMeasurable using 1
    funext q
    exact (hfactor s q).symm
  have hi (s : ℂ) (hs : 0 < s.re) :
      Integrable (fun q => c q * (d q : ℂ) ^ (s - (r / 2 : ℝ))) μ := by
    apply integrable_mellin_of_weighted_squares μ c u v d r s hd hc (hmeas s)
      hrestriction
    simpa only [v, mul_pow, mul_assoc] using hweighted s.re hs
  constructor
  · intro s hs
    rw [zeroRow_converges_iff]
    convert hi s hs using 1
    funext q
    exact hfactor s q
  · have hcm : AEStronglyMeasurable c μ :=
      (unequalRankZeroRowIntegrandContinuous F n k abv habv V V' π σ hπ hσ ψ
        ℓ ℓ' f f' (r / 2 : ℝ)).aestronglyMeasurable
    have hdm : AEMeasurable d μ :=
      (quotientDeterminantAbs_continuous abv habv n).measurable.aemeasurable
    have hdiff := hM (LeftUnipotentQuotient n F) μ c d (r / 2) hd hcm hdm
      (fun t ht => hi (t : ℂ) ht)
    have heq :
        unequalRankModelIntegral ψ abv 0 k μ
          (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f' =
        fun s : ℂ => ∫ q, c q * (d q : ℂ) ^ (s - (r / 2 : ℝ)) ∂μ := by
      funext s
      change unequalRankIntegral ψ abv 0 k μ
        (rectangularMeasure ν 0 (n + 1)) f.val f'.val s = _
      rw [zeroRow_integral]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (hfactor s)
    rw [heq]
    exact hdiff

universe uV uW

theorem squareIntegrableZeroRowAnalytic_of_estimates
    (hRestriction : SquareIntegrableWhittakerRestrictionStatement.{uF, uV})
    (hWeighted : WeightedWhittakerSquareStatement.{uF, uW}) :
    SquareIntegrableZeroRowAnalyticStatement.{uF, uV, uW} := by
  intro p hp F T n k
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ hright μ hμ ν V _ _ W _ _ π σ hiπ hπ hiσ hσ ℓ ℓ' f f'
  have hsπ : IsSmooth π := hπ.isAdmissible.1
  have hsσ : IsSmooth σ := hσ.isAdmissible.1
  obtain ⟨Φ, _, hcut⟩ := zeroRowLastRowCutoff p F T n k ψ V π hsπ ℓ f
  exact zeroRow_analytic_of_square_estimates Langlands.Analysis.mellinHalfPlane
    ψ (normalizedAbsoluteValue T)
    (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)
    k μ ν π σ hsπ hsσ ℓ ℓ' f f' Φ hcut
    (hRestriction p F T n k ψ μ hμ V π hiπ hπ ℓ f)
    ((hWeighted p F T n ψ μ hμ W σ hiσ hσ).2 ℓ' f' Φ)

theorem squareIntegrableZeroRowAnalytic_of_weighted_square
    (hWeighted : WeightedWhittakerSquareStatement.{uF, uW}) :
    SquareIntegrableZeroRowAnalyticStatement.{uF, uV, uW} :=
  squareIntegrableZeroRowAnalytic_of_estimates
    squareIntegrableWhittakerRestriction hWeighted

/-- The actual zero-row unequal-rank integral converges absolutely and is
holomorphic throughout the open half-plane `Re(s) > 0`. -/
theorem squareIntegrableZeroRowAnalytic :
    SquareIntegrableZeroRowAnalyticStatement.{uF, uV, uW} :=
  squareIntegrableZeroRowAnalytic_of_weighted_square weightedWhittakerSquare

end Langlands.RankinSelberg
