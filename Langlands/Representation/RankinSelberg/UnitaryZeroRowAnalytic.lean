import Langlands.Representation.RankinSelberg.UnitaryWeightedWhittakerSquare
import Langlands.Representation.RankinSelberg.SquareIntegrableZeroRowAnalyticStatement
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowIntegrandContinuityProof
import Langlands.Analysis.MellinHalfPlaneProof
import Langlands.Analysis.Local.QuotientTopology
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Unitary generic zero-row integrals on `Re(s) ≥ 1`

For irreducible admissible unitarizable representations `π` of `GL_(n+k+2)(F)` and `σ` of
`GL_(n+1)(F)` over a p-adic field (canonical topology), the zero-row unequal-rank JPSS
integral

`∫_{N \ GL_(n+1)} W(diag(g, 1_(k+1))) W'(g) |det g|^(s - (k+1)/2) dg`

converges absolutely for `Re(s) ≥ 1` and is holomorphic on `Re(s) > 1` (Getz–Hahn,
Proposition 11.5.1(a), the top integral of (11.19)).

The proof is that of the published `squareIntegrableZeroRowAnalytic`, with the two unitary
square estimates in place of the square-integrable ones: the restriction estimate
`∫ |W(diag(g, 1_(k+1)))|² |det g|^(-k) < ∞` (`unitaryWhittakerRestriction`) and the weighted
square `∫ |W'|² |Φ|² |det|^(2a) < ∞` for `a ≥ 1/2` (`unitaryWeightedWhittakerSquare`). The
integrand at `s` splits as `(|W| |det|^(-k/2)) · (|W'| |Φ| |det|^(Re s - 1/2))`.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnitaryGeneric

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF

section General

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]

def zeroRowProductEquiv (n : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)] :
    (LeftUnipotentQuotient n F × Matrix (Fin 0) (Fin (n + 1)) F) ≃ᵐ
      LeftUnipotentQuotient n F where
  toFun := Prod.fst
  invFun := fun q => (q, 0)
  left_inv := by intro q; exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv := by intro q; rfl
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_id.prodMk measurable_const

theorem zeroRow_integrable_iff {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (f : LeftUnipotentQuotient n F → ℂ) :
    Integrable (fun qx : LeftUnipotentQuotient n F × Matrix (Fin 0) (Fin (n + 1)) F =>
      f qx.1) (μ.prod (rectangularMeasure ν 0 (n + 1))) ↔ Integrable f μ := by
  rw [rectangularMeasure_zero_rows]
  exact measurePreserving_fst.integrable_comp_emb (zeroRowProductEquiv n).measurableEmbedding

theorem zeroRow_converges_iff (ψ : UnitaryAdditiveCharacter F)
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

theorem zeroRow_integral (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} (k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' s =
      ∫ q, unequalRankIntegrand ψ abv 0 k W W' s 0 q ∂μ := by
  simp [unequalRankIntegral]

theorem integrable_of_two_square_bounds
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

/-- The unitary splitting: `‖c‖ d^(Re s - r/2) = (u d^(-(r-1)/2)) (v d^(Re s - 1/2))`. -/
theorem integrable_mellin_of_unitary_squares
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : X → ℂ) (u v d : X → ℝ) (r : ℝ) (s : ℂ)
    (hd : ∀ x, 0 < d x) (hc : ∀ x, ‖c x‖ = u x * v x)
    (hf : AEStronglyMeasurable
      (fun x => c x * (d x : ℂ) ^ (s - (r / 2 : ℝ))) μ)
    (hu : Integrable (fun x => u x ^ 2 * d x ^ (-(r - 1))) μ)
    (hv : Integrable (fun x => v x ^ 2 * d x ^ (2 * s.re - 1)) μ) :
    Integrable (fun x => c x * (d x : ℂ) ^ (s - (r / 2 : ℝ))) μ := by
  apply integrable_of_two_square_bounds μ _ (fun x => u x * d x ^ (-(r - 1) / 2))
    (fun x => v x * d x ^ (s.re - 1 / 2)) hf
  · convert hu using 1
    funext x
    rw [mul_pow, ← Real.rpow_mul_natCast (hd x).le]
    congr 2
    push_cast
    ring
  · convert hv using 1
    funext x
    rw [mul_pow, ← Real.rpow_mul_natCast (hd x).le]
    congr 2
    push_cast
    ring
  · apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul, hc, Complex.norm_cpow_eq_rpow_re_of_pos (hd x)]
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [show s.re - r / 2 = -(r - 1) / 2 + (s.re - 1 / 2) by ring, Real.rpow_add (hd x)]
    exact le_of_eq (by ring)

omit [MeasurableSpace F] in
theorem norm_zeroRow_integrand_mk (ψ : UnitaryAdditiveCharacter F)
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

omit [MeasurableSpace F] in
theorem zeroRow_integrand_mellin (ψ : UnitaryAdditiveCharacter F)
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
theorem quotientDeterminantAbs_continuous
    [IsTopologicalRing F] (abv : AbsoluteValue F ℝ)
    (habv : Continuous abv) (n : ℕ) :
    Continuous (quotientDeterminantAbs abv n) := by
  apply (QuotientIntegration.leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  exact habv.comp Units.continuous_val.matrix_det

omit [MeasurableSpace F] in
theorem zeroRow_coefficient_norm_of_cutoff
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

/-- Convergence on `Re(s) ≥ 1` and holomorphy on `Re(s) > 1` from the two unitary square
estimates. -/
theorem zeroRow_analytic_of_unitary_square_estimates
    [IsTopologicalRing F]
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
        quotientDeterminantAbs abv n q ^ (-((0 + k : ℕ) : ℝ))) μ)
    (hweighted : ∀ a : ℝ, 1 / 2 ≤ a → Integrable
      (fun q => inverseWhittakerNorm ψ f'.val q ^ 2 *
        ‖Φ (quotientLastRow n q)‖ ^ 2 *
        quotientDeterminantAbs abv n q ^ (2 * a)) μ) :
    (∀ s : ℂ, 1 ≤ s.re →
      UnequalRankConverges ψ abv 0 k μ
        (rectangularMeasure ν 0 (n + 1)) f.val f'.val s) ∧
    DifferentiableOn ℂ
      (unequalRankModelIntegral ψ abv 0 k μ
        (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f')
      {s : ℂ | 1 < s.re} := by
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
  have hr1 : -(r - 1) = -((0 + k : ℕ) : ℝ) := by
    simp only [r]
    push_cast
    ring
  have hi (s : ℂ) (hs : 1 ≤ s.re) :
      Integrable (fun q => c q * (d q : ℂ) ^ (s - (r / 2 : ℝ))) μ := by
    apply integrable_mellin_of_unitary_squares μ c u v d r s hd hc (hmeas s)
    · rw [hr1]
      exact hrestriction
    · have h := hweighted (s.re - 1 / 2) (by linarith)
      have he : 2 * (s.re - 1 / 2) = 2 * s.re - 1 := by ring
      rw [he] at h
      simpa only [v, mul_pow, mul_assoc] using h
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
    have hshift (w : ℂ) : w - ((r / 2 - 1 : ℝ) : ℂ) = (w + 1) - ((r / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have hdiff := Langlands.Analysis.mellinHalfPlane (LeftUnipotentQuotient n F) μ c d
      (r / 2 - 1) hd hcm hdm (fun t ht => by
        rw [hshift]
        exact hi ((t : ℂ) + 1) (by simp; linarith))
    have heq :
        unequalRankModelIntegral ψ abv 0 k μ
          (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f' =
        (fun w : ℂ => ∫ q, c q * (d q : ℂ) ^ (w - ((r / 2 - 1 : ℝ) : ℂ)) ∂μ) ∘
          (fun s : ℂ => s - 1) := by
      funext s
      change unequalRankIntegral ψ abv 0 k μ
        (rectangularMeasure ν 0 (n + 1)) f.val f'.val s = _
      rw [zeroRow_integral]
      simp only [Function.comp_apply, hshift, sub_add_cancel]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (hfactor s)
    rw [heq]
    refine hdiff.comp (differentiableOn_id.sub_const 1) ?_
    intro s hs
    simp only [Set.mem_ofPred_eq, Complex.sub_re, Complex.one_re] at hs ⊢
    linarith

end General

universe uV uW

/-- **Unitary generic zero-row integrals** (Getz–Hahn, Proposition 11.5.1(a), for the zero-row
block): absolute convergence for `Re(s) ≥ 1` and holomorphy on `Re(s) > 1`. -/
theorem unitaryZeroRowAnalytic {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n k : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ ν : AdditiveHaarMeasure F.Carrier,
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
        ∀ (π : Representation ℂ
            (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
          IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
          IsAdmissible σ → Representation.IsIrreducible σ → IsUnitarizable σ →
          ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
            (ℓ' : glInverseFunctionals ψ n σ),
            ∀ (f : (coefficientModel π ℓ).toSubmodule)
              (f' : (coefficientModel σ ℓ').toSubmodule),
              (∀ s : ℂ, 1 ≤ s.re →
                UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) 0 k
                  μ (rectangularMeasure ν 0 (n + 1)) f.val f'.val s) ∧
              DifferentiableOn ℂ
                (unequalRankModelIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
                  0 k μ (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f')
                {s : ℂ | 1 < s.re} := by
  let T := F.canonicalTopologicalData
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
  intro ψ hright μ hμ ν V _ _ W _ _ π σ hπa hπi hπu hσa hσi hσu ℓ ℓ' f f'
  have hsπ : IsSmooth π := hπa.1
  have hsσ : IsSmooth σ := hσa.1
  obtain ⟨Φ, _, hcut⟩ := zeroRowLastRowCutoff p F T n k ψ V π hsπ ℓ f
  exact zeroRow_analytic_of_unitary_square_estimates
    ψ (normalizedAbsoluteValue T)
    (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom)
    k μ ν π σ hsπ hsσ ℓ ℓ' f f' Φ hcut
    (unitaryWhittakerRestriction.{uF, uV} F n k ψ μ hμ V π hπa hπi hπu ℓ f)
    ((unitaryWeightedWhittakerSquare.{uF, uW} F n ψ μ hμ W σ hσa hσi hσu).2 ℓ' f' Φ)

end Langlands.RankinSelberg.UnitaryGeneric
