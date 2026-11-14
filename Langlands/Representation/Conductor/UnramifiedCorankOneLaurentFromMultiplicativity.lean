import Langlands.Representation.Conductor.UnramifiedCorankOneLaurentStatement
import Langlands.Representation.Conductor.TrivialCharacterEpsilonReduction
import Langlands.Representation.Conductor.EssentialConductorAssembly
import Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesLFactorMultiplicativityStatement
import Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityStatement
import Langlands.Representation.RankinSelberg.LocalFieldUnramifiedTestTwist
import Langlands.Representation.RankinSelberg.UnramifiedTwistIntegrals
import Langlands.Representation.RankinSelberg.SpectralRescaling
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.Representation.RankinSelberg.InducedTailIntermediateIntegralAssembly
import Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator
import Langlands.AllField.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-!
# The Laurent clause from L- and gamma-factor multiplicativity

`UnramifiedCorankOneLaurentStatement` (JPSS 1983, Theorem (3.1)(ii), for the corank-one
integrals of `π × I(x)`) follows from the two general-field multiplicativity statements
for unramified principal series:

* `LocalFieldPrincipalSeriesGammaMultiplicativityStatement` (part (i)) supplies, through
  its gamma functional equation, a rational continuation `R` of every corank-one model
  integral `Ψ(s, W, W')`;
* `LocalFieldPrincipalSeriesLFactorMultiplicativityStatement` (part (ii)) supplies the
  L-polynomial `P_I` of `π × I(x)`, the L-polynomials `P_i` of `π × χ_{x_i}`, and
  `X^e ∏ P_i = Q₀ P_I`.

With the convergence hypothesis of the Laurent statement, `R` is a zeta value of the
block `j = k = 0`, so `P_I R` is a Laurent polynomial. The unramified twist identifies
`P_i` with `P(x_i X)` for the standard L-polynomial `P` of `π`, and the product relation
gives the Laurent clause.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial QuotientIntegration
open Langlands.Conductor.UnramifiedPrincipalSeries Langlands.GeneralLinear.Iwasawa

universe uF uV

section Algebra

/-- A Laurent polynomial evaluates to `z^N Q(z)` at every nonzero `z`. -/
theorem exists_laurentEval_eq_zpow_mul (b : LaurentCoefficients) :
    ∃ (N : ℤ) (Q : ℂ[X]), ∀ z : ℂˣ, laurentEval z b = (z : ℂ) ^ N * Q.eval (z : ℂ) := by
  obtain ⟨m, Q, hQ⟩ := LaurentPolynomial.exists_T_pow b
  refine ⟨-(m : ℤ), Q, fun z => ?_⟩
  have h := congrArg (laurentEval z) hQ
  rw [laurentEval_toLaurent, map_mul, laurentEval_T] at h
  rw [h, mul_comm (laurentEval z b), ← mul_assoc, ← zpow_add₀ (Units.ne_zero z),
    neg_add_cancel, zpow_zero, one_mul]

end Algebra

section Twist

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Twisting the rank-one test by an unramified character `|·|^u` transports the
character zeta values of `π × 1` by `e`. -/
theorem characterZetaValues_unramified [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ₀ : Measure (LeftUnipotentQuotient 0 F)) (u : ℂ)
    (e : RationalFunctions ≃ RationalFunctions)
    (hshift : ∀ (f : ℂ → ℂ) (R : RationalFunctions),
      HasRationalContinuation q (fun s => f (s + u)) (e R) ↔ HasRationalContinuation q f R)
    (χ : Fˣ →* ℂˣ) (hχ : ∀ x : Fˣ, (χ x : ℂ) = (abv (x : F) : ℂ) ^ u) {k : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F) V) :
    characterZetaValues q ψ abv μ₀ χ (k + 1) π =
      e '' characterZetaValues q ψ abv μ₀ 1 (k + 1) π := by
  let : MeasurableSpace (Matrix (Fin 0) (Fin (0 + 1)) F) := ⊤
  change unequalRankZetaValues q ψ abv 0 k μ₀ (Measure.dirac 0)
      (π.comp (characterPairRank k).toMonoidHom) (rankOneCharacter χ) =
    e '' unequalRankZetaValues q ψ abv 0 k μ₀ (Measure.dirac 0)
      (π.comp (characterPairRank k).toMonoidHom) (rankOneCharacter 1)
  rw [← HighlyRamified.twist_rankOneCharacter_one χ]
  exact unequalRankZetaValues_unramified_right ψ abv q u e hshift χ hχ 0 k μ₀
    (Measure.dirac 0) _ _

/-- The L-polynomial of `π × χ_z`, `χ_z` the unramified character with `χ_z(ϖ) = z`, is
`P(zX)` for the standard L-polynomial `P` of `π`. -/
theorem isCharacterLPolynomial_unramified [ValuativeRel F]
    [MeasurableSpace (LeftUnipotentQuotient 0 F)] {q : ℕ} (hq : 1 < q)
    (ψ : UnitaryAdditiveCharacter F) {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (habv : abv (ϖ : F) = (q : ℝ)⁻¹)
    (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (μ₀ : Measure (LeftUnipotentQuotient 0 F)) {k : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F) V) {P : ℂ[X]}
    (hP : IsCharacterLPolynomial q ψ abv μ₀ 1 π P) (z : ℂˣ) :
    IsCharacterLPolynomial q ψ abv μ₀ (character hϖ z) π (P.comp (C (z : ℂ) * X)) := by
  obtain ⟨u, hu⟩ := HighlyRamified.exists_spectralShiftUnit_eq hq z
  have hχ := unramifiedCharacter_eq_abv_cpow hq hϖ habv hunit hu
  unfold IsCharacterLPolynomial at hP ⊢
  rw [characterZetaValues_unramified q ψ abv μ₀ u
    (rationalRescale (spectralShiftUnit q hq u)).toEquiv
    (fun f R => hasRationalContinuation_shift_iff hq f R u) _ hχ π, ← hu]
  simpa only [AlgEquiv.toEquiv_eq_coe, AlgEquiv.coe_toEquiv] using
    hP.rescale (spectralShiftUnit q hq u)

end Twist

section ZeroBlock

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- With zero rectangular rows, convergence of the block `j = k = 0` is corank-one
convergence. -/
theorem unequalRankConverges_rectangular_zero_iff (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (W : WhittakerFunctions ψ (n + 1))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    UnequalRankConverges ψ abv 0 0 μ (rectangularMeasure ν 0 (n + 1)) W W' s ↔
      CorankOneConverges ψ abv μ W W' s := by
  rw [rectangularMeasure_zero_rows,
    InducedTailIntermediate.unequalRankConverges_zero_rows_iff]
  unfold CorankOneConverges
  have hfun : unequalRankIntegrand ψ abv 0 0 W W' s 0 = corankOneIntegrand ψ abv W W' s :=
    funext fun q => unequalRankIntegrand_zero_zero ψ abv W W' s 0 q
  rw [hfun]

/-- With zero rectangular rows, the integral of the block `j = k = 0` is the corank-one
integral. -/
theorem unequalRankIntegral_rectangular_zero (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F) (W : WhittakerFunctions ψ (n + 1))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv 0 0 μ (rectangularMeasure ν 0 (n + 1)) W W' s =
      corankOneIntegral ψ abv μ W W' s := by
  rw [rectangularMeasure_zero_rows]
  exact unequalRankIntegral_zero_zero ψ abv μ W W' s

end ZeroBlock

/-- `UnramifiedCorankOneLaurentStatement` from JPSS 1983, Theorem (3.1), parts (i) and (ii),
for unramified principal series over every nonarchimedean local field. -/
theorem unramifiedCorankOneLaurent_of_multiplicativity
    (hL : LocalFieldPrincipalSeriesLFactorMultiplicativityStatement.{uF, uV})
    (hG : LocalFieldPrincipalSeriesGammaMultiplicativityStatement.{uF, uV}) :
    UnramifiedCorankOneLaurentStatement.{uF, uV} := by
  intro F _ _ _ _ n mG bG mU bU mQ mQ₀ mG₁ bG₁ q ψ abv ϖ μ h V _ _ π hπ ℓ hℓ P hP x ℓ'
    hℓ' W W' hconv
  have bQ : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  have bQ₀ : BorelSpace (LeftUnipotentQuotient 0 F) := h.borel_rankOne
  obtain rfl := bG.measurable_eq
  obtain rfl := bU.measurable_eq
  obtain rfl := bG₁.measurable_eq
  obtain rfl := bQ.measurable_eq
  obtain rfl := bQ₀.measurable_eq
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
  have : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (Langlands.GeneralLinear 1 F) := borel _
  have : BorelSpace (Langlands.GeneralLinear 1 F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let : MeasurableSpace (LeftUnipotentQuotient 0 F) := borel _
  have hT2 : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have hTD : TotallyDisconnectedSpace F :=
    Langlands.BruhatTits.localField_totallyDisconnectedSpace F
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have hq1 : 1 < q := h.one_lt_q
  have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq1
  have hq : IsResidueCardinality (F := F) q := h.residueCardinality
  have hsdF := Langlands.AllField.HarmonicAnalysis.padicSelfDualMeasureExists F
    (LocalFieldData.ofInstances F)
  dsimp only [Langlands.AllField.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement,
    LocalFieldData.ofInstances] at hsdF
  obtain ⟨htd, hsd⟩ := hsdF
  obtain ⟨ν, hν⟩ := hsd ψ
  have hπW : IsOfWhittakerType (n + 1) (standardCharacter ψ (n + 1)) π :=
    isOfWhittakerType_of_isGeneric_localField hπ
  -- The L-polynomials from part (ii).
  obtain ⟨PI, Pi, hPI, hPi, Q₀, e, hprod⟩ :=
    hL F q hq abv ϖ h.uniformizer h.abv_uniformizer h.abv_unit ψ ν hν (n + 1) n π hπW x
  have hPIp := (isGeneralSymmetricLPolynomial_of_le (Nat.le_succ n)).1 hPI
  obtain ⟨⟨hinv, -⟩, hPIall⟩ := hPIp
  have hPIμ := @hPIall hinv μ h.measure
  have hgen : IsNormalizedGenerator
      (unequalRankZetaValues q ψ abv 0 0 μ (rectangularMeasure ν 0 (n + 1)) π
        (principalSeries h.uniformizer n h.residueCardinality x)) PI :=
    (isPairLPolynomial_of_lt (Nat.lt_succ_self n)).1 hPIμ 0 0 rfl
  -- The rational continuation from part (i).
  obtain ⟨G, -, hGprod⟩ :=
    hG F q hq abv ϖ h.uniformizer h.abv_uniformizer h.abv_unit ψ ν hν (n + 1) n π hπW x
  have hGp := (isGeneralSymmetricGammaFactor_of_le (Nat.le_succ n)).1 hGprod
  have hGu : IsUnequalRankGammaFactor (Nat.lt_succ_self n) q ψ abv ν π
      (principalSeries h.uniformizer n h.residueCardinality x) (∏ i, G i) := by
    unfold IsGeneralPairGammaFactor IsPairGammaFactor at hGp
    rwa [dite_eq_left (Nat.lt_succ_self n)] at hGp
  obtain ⟨-, -, -, hGall⟩ := hGu
  obtain ⟨ζ, -, hblock⟩ := @hGall hinv μ h.measure ℓ ℓ' hℓ hℓ'
  obtain ⟨R, -, hR, -, -⟩ := (hblock 0 0 rfl).2 W W'
  -- `R` is a zeta value of the block `j = k = 0`.
  have hconv' : ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      UnequalRankConverges ψ abv 0 0 μ (rectangularMeasure ν 0 (n + 1)) W.val W'.val s := by
    obtain ⟨a, ha⟩ := hconv
    exact ⟨a, fun s hs =>
      (unequalRankConverges_rectangular_zero_iff ψ abv μ ν W.val W'.val s).2 (ha s hs)⟩
  have hmem : R ∈ unequalRankZetaValues q ψ abv 0 0 μ (rectangularMeasure ν 0 (n + 1)) π
      (principalSeries h.uniformizer n h.residueCardinality x) :=
    unequalRankModel_mem_zetaValues q ψ abv 0 0 μ _ ℓ ℓ' W W' hconv' hR
  obtain ⟨b, hb⟩ := hgen.clearsDenominators (mem_zetaSpan hmem)
  -- The rank-one factors are the unramified rescalings of `P`.
  have hPi_eq : ∀ i, Pi i = P.comp (C (x i : ℂ) * X) := by
    intro i
    have h1 := (isGeneralSymmetricLPolynomial_of_le (Nat.zero_le (n + 1))).1 (hPi i)
    obtain ⟨-, h2⟩ := h1
    let : MeasurableSpace (upperUnipotent (0 + 1) F) := borel _
    have : BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
    have h3 :=
      (h2 (rankOneQuotientHaar F) (rankOneQuotientHaar_isCompatible F)).isCharacterLPolynomial
    have h4 := isCharacterLPolynomial_unramified hq1 ψ h.uniformizer h.abv_uniformizer
      h.abv_unit (rankOneQuotientHaar F) π hP (x i)
    exact IsNormalizedGenerator.unique h3 h4
  obtain ⟨N, Q, hNQ⟩ :=
    exists_laurentEval_eq_zpow_mul (b * Polynomial.toLaurent Q₀ * LaurentPolynomial.T (-(e : ℤ)))
  obtain ⟨a₁, ha₁⟩ := hR
  refine ⟨a₁, N, Q, fun s hs => ?_⟩
  obtain ⟨hden, hval⟩ := ha₁ s hs
  set z : ℂˣ := spectralUnit hq0 s with hz
  have hzs : (z : ℂ) = spectralPoint q s := rfl
  have hb' := laurentEval_eq_of_laurentToRatFunc_eq z hb (hzs ▸ hden)
  have hint : corankOneIntegral ψ abv μ W.val W'.val s =
      RatFunc.eval (RingHom.id ℂ) (z : ℂ) R := by
    rw [hzs, ← hval]
    exact (unequalRankIntegral_rectangular_zero ψ abv μ ν W.val W'.val s).symm
  have hp := congrArg (Polynomial.eval (z : ℂ)) hprod
  simp only [eval_mul, eval_pow, eval_X] at hp
  have hP' : (∏ i, P.comp (C (x i : ℂ) * X)) = ∏ i, Pi i :=
    Finset.prod_congr rfl fun i _ => (hPi_eq i).symm
  rw [← hzs, hint, hP', ← hNQ z]
  simp only [map_mul, laurentEval_toLaurent, laurentEval_T, hb']
  have hz0 : (z : ℂ) ≠ 0 := Units.ne_zero z
  have hA : (∏ i, Pi i).eval (z : ℂ) =
      (z : ℂ) ^ (-(e : ℤ)) * (Q₀.eval (z : ℂ) * PI.eval (z : ℂ)) := by
    rw [← hp, ← mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hz0),
      one_mul]
  rw [hA]
  ring

end Langlands.Conductor
