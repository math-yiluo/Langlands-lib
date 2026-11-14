import Langlands.Representation.Conductor.TrivialCharacterEpsilonReduction
import Langlands.Representation.Conductor.SphericalCorankOneRankOneGamma
import Langlands.Representation.Conductor.SphericalCorankOneSphericalEquation
import Langlands.Representation.Conductor.UnramifiedSphericalWhittaker
import Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationStatement
import Langlands.Representation.Conductor.SphericalCorankOneConvergenceStatement
import Langlands.Representation.Conductor.OrderedUnramifiedSphericalFunctional
import Langlands.Representation.Conductor.EssentialDualSetup
import Langlands.Representation.Conductor.EssentialConductorAssembly
import Langlands.Representation.RankinSelberg.LocalFieldUnequalRankAnalyticStatement
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.RankinSelberg.WhittakerTypeFromMultiplicityProof
import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof

/-!
# Reduction of the spherical corank-one functional equation to three inputs

The target `SphericalCorankOneFunctionalEquationStatement` follows from three
propositions: the all-field unequal-rank convergence and rationality
`LocalFieldUnequalRankAnalyticStatement`, the corank-one convergence
`SphericalCorankOneConvergenceStatement`, and `PrincipalSeriesGammaInput` (defined here:
the gamma factor of `π × I(x)` is the product of rescaled gamma factors of `π × 1`).
The normalized inverse-character functional on `I(x)` is
`exists_glInverseFunctional_sphericalWhittaker`, and the minus-one scalar on the unramified
principal series is `hasModelMinusOneScalar_principalSeries`. The three inputs are
discharged in `SphericalCorankOneFunctionalEquationProof`.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCorankOne

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial
open Langlands.RankinSelberg LocalFactor Langlands.GeneralLinear.Iwasawa
open Langlands.Conductor.UnramifiedPrincipalSeries

universe uF uV uW

/-- Gamma input: under Jacquet's normalizations, a gamma factor `G` of `π × 1`
gives the gamma factor `∏ i, G(x_i X)` of `π × I(x)` for unitary `x`
(JPSS 1983, Theorem (3.1), with the unramified twist). -/
def PrincipalSeriesGammaInput : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F] (n : ℕ)
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
    [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
    [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (h : IsJacquetNormalization q ψ abv ϖ μ)
    (ν : AdditiveHaarMeasure F), IsSelfDual ψ ν →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V),
      IsGeneric ψ (n + 1) π →
    ∀ G : RationalFunctions, IsPairGammaFactor q ψ abv ν π (rankOneCharacter 1) G →
    ∀ x : Fin (n + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) →
      IsPairGammaFactor q ψ abv ν π
        (principalSeries h.uniformizer n h.residueCardinality x)
        (∏ i, rationalRescale (x i) G)

/-- The convergence part of the all-field unequal-rank statement, for a rank `r + 1`
written as `n + (j + k + 1) + 1` through an equation `hr`. -/
theorem unequalRankConvergenceAt_of_analytic
    (hA : LocalFieldUnequalRankAnalyticStatement.{uF, uV, uW})
    {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
    [MeasurableSpace F] [BorelSpace F] {n : ℕ}
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
    [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
    [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
    {q : ℕ} (hqF : q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer))
    {abv : AbsoluteValue F ℝ} {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (habv : abv (ϖ : F) = (q : ℝ)⁻¹)
    (habv1 : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    (ψ : UnitaryAdditiveCharacter F) (μ : Measure (LeftUnipotentQuotient n F))
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n) μ)
    (ν : AdditiveHaarMeasure F) (j k : ℕ) {r : ℕ} (hr : r = n + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    UnequalRankConvergenceAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ' := by
  subst hr
  exact (hA F n j k q hqF abv ϖ hϖ habv habv1 ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ').1

/-- The product of the rescaled dual L-polynomials is nonzero: its value at `0` is `1`. -/
theorem prod_comp_ne_zero {n : ℕ} {P : ℂ[X]} (hP : P.coeff 0 = 1) (x : Fin (n + 1) → ℂˣ) :
    (∏ i, P.comp (C ((x i : ℂˣ) : ℂ) * X)) ≠ 0 := by
  intro h0
  have h1 := congrArg (Polynomial.eval 0) h0
  simp only [eval_prod, eval_comp, eval_mul, eval_C, eval_X, mul_zero, eval_zero] at h1
  rw [← coeff_zero_eq_eval_zero, hP, Finset.prod_const_one] at h1
  exact one_ne_zero h1

/-- The target, from the three inputs. -/
theorem sphericalCorankOneFunctionalEquation_of_inputs
    (hA : LocalFieldUnequalRankAnalyticStatement.{uF, uV, 0})
    (hS : SphericalCorankOneConvergenceStatement.{uF, uV})
    (hM : PrincipalSeriesGammaInput.{uF, uV}) :
    SphericalCorankOneFunctionalEquationStatement.{uF, uV} := by
  intro F _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ q ψ abv ϖ μ h h' ν hν V _ _ π hπ ℓ hℓ ℓ' hℓ'
    c m hε P Pdual hP hPd v x hx
  let := h.borel
  let := h.borel_rankOne
  have hq1 : 1 < q := h.one_lt_q
  have hqR : IsResidueCardinality (F := F) q := h.residueCardinality
  let δ : ℂˣ := Units.mk0 ((q : ℂ)⁻¹)
    (inv_ne_zero (Nat.cast_ne_zero.mpr (by omega)))
  have hδ : (δ : ℂ) = (q : ℂ)⁻¹ := rfl
  have hW : IsOfWhittakerType (n + 1) (standardCharacter ψ (n + 1)) π :=
    isOfWhittakerType_of_isGeneric_localField hπ
  have hπd := isGeneric_inverseTransposePullback ψ π hπ
  have hWd : IsOfWhittakerType (n + 1) (standardCharacter (ψ.scale (-1)) (n + 1))
      (inverseTransposePullback π) :=
    isOfWhittakerType_of_isGeneric_localField hπd
  have h1 : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) :=
    (isOfWhittakerType_standard_iff_inverse ψ _).mp (isOfWhittakerType_rankOneCharacter_one ψ)
  have h1d : IsOfWhittakerType 0 (inverseStandardCharacter (ψ.scale (-1)) 0)
      (inverseTransposePullback (rankOneCharacter (1 : Fˣ →* ℂˣ))) := by
    rw [inverseTransposePullback_rankOneCharacter_one]
    exact (isOfWhittakerType_standard_iff_inverse _ _).mp
      (isOfWhittakerType_rankOneCharacter_one _)
  have hG₁ := isPairGammaFactor_rankOne_of_convergence (N := n) hq1 hδ hW hWd
    (fun ℓ₁ ℓ₂ h₁ h₂ => unequalRankConvergenceAt_of_analytic hA h.residueCardinality
      h.uniformizer h.abv_uniformizer h.abv_unit ψ (rankOneQuotientHaar F)
      (rankOneQuotientHaar_isCompatible F) ν 0 n _ π _ hW h1 ℓ₁ ℓ₂ h₁ h₂)
    (fun ℓ₁ ℓ₂ h₁ h₂ => unequalRankConvergenceAt_of_analytic hA h.residueCardinality
      h.uniformizer h.abv_uniformizer h.abv_unit (ψ.scale (-1)) (rankOneQuotientHaar F)
      (rankOneQuotientHaar_isCompatible F) ν 0 n _ _ _ hWd h1d _ _
      (firstDualFunctional_ne_zero ψ π h₁) (secondDualFunctional_ne_zero ψ _ h₂))
    hε hP hPd
  have hG := hM F n q ψ abv ϖ μ h ν hν π hπ _ hG₁ x hx
  rw [prod_rationalRescale_rationalGammaExpression] at hG
  have hmono : Monotone (fun i => ‖(x i : ℂ)‖) := by
    intro i j _
    simp only [hx, le_refl]
  obtain ⟨lam, hlam, hlamf⟩ :=
    exists_glInverseFunctional_sphericalWhittaker h.uniformizer n hqR x hmono h.conductor
  have hxmem : inverseSphericalWhittaker h.conductor.1 h.uniformizer q x ∈
      (coefficientModel (principalSeries h.uniformizer n hqR x) lam).toSubmodule :=
    ⟨sphericalSection h.uniformizer n hqR x, Subtype.ext (funext hlamf)⟩
  have hQd : (∏ i, Pdual.comp (C ((x⁻¹ i : ℂˣ) : ℂ) * X)) ≠ 0 :=
    prod_comp_ne_zero hPd.1 x⁻¹
  have hℓ'ne : ℓ'.val ≠ 0 := by
    rw [hℓ']
    exact scaledDualFunctional_ne_zero ψ π ℓ hℓ
  obtain ⟨-, -, hconv⟩ := hS F n q ψ abv ϖ μ h π hπ ℓ hℓ
  obtain ⟨-, -, hconvd⟩ := hS F n q (ψ.scale (-1)) abv ϖ μ h' _ hπd ℓ' hℓ'ne
  refine ⟨hconv ⟨_, v, rfl⟩ x, hconvd ⟨_, v, rfl⟩ x⁻¹, ?_⟩
  exact normalizedFunctionalEquation_of_sphericalGammaFactor hq1 hδ hQd hG μ h.measure
    ℓ hℓ ℓ' hℓ' lam hlam (hasModelMinusOneScalar_principalSeries h.uniformizer n hqR x lam)
    h.conductor.1
    h'.conductor.1 h.uniformizer x hxmem v

end Langlands.Conductor.SphericalCorankOne
