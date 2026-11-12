import Langlands.Representation.RankinSelberg.UnramifiedTwistStatement
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaIntegrals
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaScalar
import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.Representation.Twist.AlgebraProof

/-!
# Unramified twists of pair epsilon factors

Twisting either member of a pair by `|det|^u` shifts every JPSS integral of the
fixed-functional epsilon equation: the forward integrals from `s` to `s + u` and
the dual integrals from `1 - s` to `1 - s - u` (module
`UnramifiedTwistGammaIntegrals`). Hence the normalized generators are rescaled,
the minus-one scalar is kept, and the epsilon monomial `c q^(-ms)` becomes
`(c q^(-mu)) q^(-ms)`. This proves `UnramifiedTwistEpsilonStatement`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory QuotientIntegration Polynomial

universe uF uV uW

section Scalar

variable {q : ℕ} (hq : 1 < q)

include hq in
/-- Multiplying the coefficient by `q^(-mu)` shifts the epsilon monomial by `u`. -/
theorem epsilonMonomial_shift (c : ℂˣ) (m : ℤ) (s u : ℂ) :
    epsilonMonomial q (c * spectralShiftUnit q hq u ^ m) m s =
      epsilonMonomial q c m (s + u) := by
  unfold epsilonMonomial
  rw [spectralPoint_add hq, mul_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val,
    coe_spectralShiftUnit]
  ring

include hq in
/-- Substituting `q^(-u) X` evaluates a polynomial at the shifted spectral point. -/
theorem eval_spectralRescale (P : ℂ[X]) (u s : ℂ) :
    (P.comp (C (spectralShiftUnit q hq u : ℂ) * X)).eval (spectralPoint q s) =
      P.eval (spectralPoint q (s + u)) := by
  rw [eval_comp, eval_mul, eval_C, eval_X, coe_spectralShiftUnit, spectralPoint_add hq]

/-- Translating the forward data by `u` and the dual data by `-u` transports the
normalized functional equation, with epsilon coefficient multiplied by
`q^(-mu)` and the same exponent `m`. -/
theorem NormalizedFunctionalEquation.shift
    {P Pdual : ℂ[X]} {ζ c : ℂˣ} {e : ℕ} {m : ℤ} {R Rdual : RationalFunctions}
    (h : NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual) (u : ℂ) :
    NormalizedFunctionalEquation q
      (P.comp (C (spectralShiftUnit q hq u : ℂ) * X))
      (Pdual.comp (C (spectralShiftUnit q hq (-u) : ℂ) * X))
      ζ (c * spectralShiftUnit q hq u ^ m) e m
      (rationalRescale (spectralShiftUnit q hq u) R)
      (rationalRescale (spectralShiftUnit q hq (-u)) Rdual) := by
  intro s hR hD
  have hR' := (spectralRescale_denom_ne_zero_iff hq u R s).mp hR
  have hD' := (spectralRescale_denom_ne_zero_iff hq (-u) Rdual (1 - s)).mp hD
  have hreflect : 1 - s + -u = 1 - (s + u) := by ring
  rw [spectralRescale_eval hq u R s hR', spectralRescale_eval hq (-u) Rdual (1 - s) hD',
    eval_spectralRescale hq, eval_spectralRescale hq, hreflect, epsilonMonomial_shift hq]
  exact h (s + u) hR' (by simpa only [hreflect] using hD')

end Scalar

namespace UnramifiedEpsilonTwist

section EqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)
  (q : ℕ) (hq : 1 < q)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (L : glFunctionals ψ n π) (L' : glInverseFunctionals ψ n σ)

omit [IsTopologicalRing F] [MeasurableSpace F] in
include hprod in
/-- The forward equal-rank values of the twisted pair are the `u`-rescaled values. -/
theorem equal_values :
    equalRankRationalValues q ψ abv μ
        (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
        (UnramifiedGammaTwist.functional χ₁ π L) (UnramifiedGammaTwist.functional χ₂ σ L') =
      rationalRescale (spectralShiftUnit q hq u) ''
        equalRankRationalValues q ψ abv μ π σ L L' := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    rw [UnramifiedGammaTwist.equal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w Φ] at hR
    refine ⟨rationalRescale (spectralShiftUnit q hq u)⁻¹ R,
      ⟨modelMap _ _ v, modelMap _ _ w, Φ, ?_⟩, rationalRescale_apply_inv _ _⟩
    rw [← hasRationalContinuation_shift_iff hq _ _ u, rationalRescale_apply_inv]
    exact hR
  · rintro ⟨R₀, ⟨f, f', Φ, hR⟩, rfl⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    refine ⟨modelMap _ _ v, modelMap _ _ w, Φ, ?_⟩
    rw [UnramifiedGammaTwist.equal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w Φ]
    exact hR.shift hq u

omit [MeasurableSpace F] in
include h₁ h₂ hprod in
/-- The dual equal-rank values of the twisted pair are the `(-u)`-rescaled values. -/
theorem equal_dual_values :
    dualEqualRankRationalValues q ψ abv μ
        (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
        (UnramifiedGammaTwist.functional χ₁ π L) (UnramifiedGammaTwist.functional χ₂ σ L') =
      rationalRescale (spectralShiftUnit q hq (-u)) ''
        dualEqualRankRationalValues q ψ abv μ π σ L L' := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    rw [UnramifiedGammaTwist.equal_dual ψ abv χ₁ χ₂ u h₁ h₂ hprod μ π σ L L' v w Φ] at hR
    simp only [sub_eq_add_neg] at hR
    refine ⟨rationalRescale (spectralShiftUnit q hq (-u))⁻¹ R,
      ⟨modelMap _ _ v, modelMap _ _ w, Φ, ?_⟩, rationalRescale_apply_inv _ _⟩
    rw [← hasRationalContinuation_shift_iff hq _ _ (-u), rationalRescale_apply_inv]
    exact hR
  · rintro ⟨R₀, ⟨f, f', Φ, hR⟩, rfl⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    refine ⟨modelMap _ _ v, modelMap _ _ w, Φ, ?_⟩
    rw [UnramifiedGammaTwist.equal_dual ψ abv χ₁ χ₂ u h₁ h₂ hprod μ π σ L L' v w Φ]
    simpa only [sub_eq_add_neg] using hR.shift hq (-u)

include h₁ h₂ hprod in
/-- Transport of the equal-rank fixed-functional epsilon equation. -/
theorem equal_equation {c : ℂˣ} {m : ℤ}
    (h : EqualRankEpsilonEquation q ψ abv μ ν π σ L L' c m) :
    EqualRankEpsilonEquation q ψ abv μ ν
      (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
      (UnramifiedGammaTwist.functional χ₁ π L) (UnramifiedGammaTwist.functional χ₂ σ L')
      (c * spectralShiftUnit q hq u ^ m) m := by
  obtain ⟨ζ, P, Pdual, hζ, hP, hPd, hall⟩ := h
  refine ⟨ζ, P.comp (C (spectralShiftUnit q hq u : ℂ) * X),
    Pdual.comp (C (spectralShiftUnit q hq (-u) : ℂ) * X),
    UnramifiedGammaTwist.minusOne χ₂ h₂ σ L' hζ, ?_, ?_, ?_⟩
  · rw [equal_values ψ abv χ₁ χ₂ u hprod q hq μ π σ L L']
    exact hP.rescale _
  · rw [equal_dual_values ψ abv χ₁ χ₂ u h₁ h₂ hprod q hq μ π σ L L']
    exact hPd.rescale _
  · intro f f' Φ
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    obtain ⟨Φhat, R, Rd, hΦ, hR, hRd, heq⟩ := hall (modelMap _ _ v) (modelMap _ _ w) Φ
    refine ⟨Φhat, rationalRescale (spectralShiftUnit q hq u) R,
      rationalRescale (spectralShiftUnit q hq (-u)) Rd, hΦ, ?_, ?_, heq.shift hq u⟩
    · rw [UnramifiedGammaTwist.equal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w Φ]
      exact hR.shift hq u
    · rw [UnramifiedGammaTwist.equal_dual ψ abv χ₁ χ₂ u h₁ h₂ hprod μ π σ L L' v w Φhat]
      simpa only [sub_eq_add_neg] using hRd.shift hq (-u)

end EqualRank

section UnequalRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)
  {r n : ℕ} (hnr : n < r) (q : ℕ) (hq : 1 < q)
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (L : glFunctionals ψ r π) (L' : glInverseFunctionals ψ n σ)

omit [IsTopologicalRing F] in
include hprod in
/-- The forward values of every rectangular block of the twisted pair are the
`u`-rescaled values. -/
theorem unequal_values (j k : ℕ) (hr : r = n + (j + k + 1)) :
    unequalRankValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
        (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
        (UnramifiedGammaTwist.functional χ₁ π L) (UnramifiedGammaTwist.functional χ₂ σ L') =
      rationalRescale (spectralShiftUnit q hq u) ''
        unequalRankValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
          π σ L L' := by
  rw [unequalRankValuesAt_eq, unequalRankValuesAt_eq]
  ext R
  constructor
  · rintro ⟨f, f', hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    rw [UnramifiedGammaTwist.unequal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w j k hr]
      at hR
    refine ⟨rationalRescale (spectralShiftUnit q hq u)⁻¹ R,
      ⟨modelMap _ _ v, modelMap _ _ w, ?_⟩, rationalRescale_apply_inv _ _⟩
    rw [← hasRationalContinuation_shift_iff hq _ _ u, rationalRescale_apply_inv]
    exact hR
  · rintro ⟨R₀, ⟨f, f', hR⟩, rfl⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    refine ⟨modelMap _ _ v, modelMap _ _ w, ?_⟩
    rw [UnramifiedGammaTwist.unequal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w j k hr]
    exact hR.shift hq u

include h₁ h₂ hprod in
/-- The dual values of every rectangular block of the twisted pair are the
`(-u)`-rescaled values. -/
theorem unequal_dual_values (j k : ℕ) (hr : r = n + (j + k + 1)) :
    dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν
        (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
        (UnramifiedGammaTwist.functional χ₁ π L) (UnramifiedGammaTwist.functional χ₂ σ L') =
      rationalRescale (spectralShiftUnit q hq (-u)) ''
        dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν π σ L L' := by
  ext R
  constructor
  · rintro ⟨f, f', hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    rw [UnramifiedGammaTwist.unequal_dual ψ abv χ₁ χ₂ u h₁ h₂ hprod μ π σ L L' v w
      hnr j k hr ν] at hR
    simp only [sub_eq_add_neg] at hR
    refine ⟨rationalRescale (spectralShiftUnit q hq (-u))⁻¹ R,
      ⟨modelMap _ _ v, modelMap _ _ w, ?_⟩, rationalRescale_apply_inv _ _⟩
    rw [← hasRationalContinuation_shift_iff hq _ _ (-u), rationalRescale_apply_inv]
    exact hR
  · rintro ⟨R₀, ⟨f, f', hR⟩, rfl⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    refine ⟨modelMap _ _ v, modelMap _ _ w, ?_⟩
    rw [UnramifiedGammaTwist.unequal_dual ψ abv χ₁ χ₂ u h₁ h₂ hprod μ π σ L L' v w
      hnr j k hr ν]
    simpa only [sub_eq_add_neg] using hR.shift hq (-u)

include h₁ h₂ hprod in
/-- Transport of the unequal-rank fixed-functional epsilon equation, for every
rectangular block. -/
theorem unequal_equation {c : ℂˣ} {m : ℤ}
    (h : UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ L L' c m) :
    UnequalRankEpsilonEquation hnr q ψ abv μ ν
      (Langlands.twist (χ₁.comp determinant) π) (Langlands.twist (χ₂.comp determinant) σ)
      (UnramifiedGammaTwist.functional χ₁ π L) (UnramifiedGammaTwist.functional χ₂ σ L')
      (c * spectralShiftUnit q hq u ^ m) m := by
  obtain ⟨ζ, P, Pdual, hζ, hall⟩ := h
  refine ⟨ζ, P.comp (C (spectralShiftUnit q hq u : ℂ) * X),
    Pdual.comp (C (spectralShiftUnit q hq (-u) : ℂ) * X),
    UnramifiedGammaTwist.minusOne χ₂ h₂ σ L' hζ, ?_⟩
  intro j k hr
  obtain ⟨hP, hPd, hFE⟩ := hall j k hr
  refine ⟨?_, ?_, ?_⟩
  · rw [unequal_values ψ abv χ₁ χ₂ u hprod q hq μ ν π σ L L' j k hr]
    exact hP.rescale _
  · rw [unequal_dual_values ψ abv χ₁ χ₂ u h₁ h₂ hprod hnr q hq μ ν π σ L L' j k hr]
    exact hPd.rescale _
  · intro f f'
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨w, rfl⟩ := modelMap_surjective _ _ f'
    obtain ⟨R, Rd, hR, hRd, heq⟩ := hFE (modelMap _ _ v) (modelMap _ _ w)
    refine ⟨rationalRescale (spectralShiftUnit q hq u) R,
      rationalRescale (spectralShiftUnit q hq (-u)) Rd, ?_, ?_, heq.shift hq u⟩
    · rw [UnramifiedGammaTwist.unequal_forward ψ abv χ₁ χ₂ u hprod μ π σ L L' v w j k hr]
      exact hR.shift hq u
    · rw [UnramifiedGammaTwist.unequal_dual ψ abv χ₁ χ₂ u h₁ h₂ hprod μ π σ L L' v w
        hnr j k hr ν]
      simpa only [sub_eq_add_neg] using hRd.shift hq (-u)

end UnequalRank

section Relations

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (hq : 1 < q) (ψ : UnitaryAdditiveCharacter F)
  (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
  (χ₁ χ₂ : Fˣ →* ℂˣ) (u : ℂ)
  (h₁ : χ₁ (-1) = 1) (h₂ : χ₂ (-1) = 1)
  (hprod : ∀ x : Fˣ, (χ₁ x : ℂ) * (χ₂ x : ℂ) = (abv (x : F) : ℂ) ^ u)

include h₁ h₂ hprod in
/-- Transport of the complete equal-rank epsilon relation. Functionals of the
twisted representations are untwisted without changing their linear maps. -/
theorem equal_factor
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {e : ℂˣ × ℤ} (h : IsEqualRankEpsilonFactor q ψ abv ν π σ e) :
    IsEqualRankEpsilonFactor q ψ abv ν
      (Langlands.twist (χ₁.comp determinant) π)
      (Langlands.twist (χ₂.comp determinant) σ)
      (e.1 * spectralShiftUnit q hq u ^ e.2, e.2) := by
  obtain ⟨hμ, ⟨L, hL⟩, ⟨L', hL'⟩, hall⟩ := h
  refine ⟨hμ, ⟨UnramifiedGammaTwist.functional χ₁ π L, hL⟩,
    ⟨UnramifiedGammaTwist.functional χ₂ σ L', hL'⟩, ?_⟩
  intro hinv μ hμc K K' hK hK'
  let L₀ := untwistFunctional _ _ (χ₁.comp determinant)
    (determinantCharacter_unipotent χ₁) π K
  let L₀' := untwistFunctional _ _ (χ₂.comp determinant)
    (determinantCharacter_unipotent χ₂) σ K'
  exact equal_equation ψ abv χ₁ χ₂ u h₁ h₂ hprod q hq μ ν π σ L₀ L₀'
    (@hall hinv μ hμc L₀ L₀' hK hK')

include h₁ h₂ hprod in
/-- Transport of the complete unequal-rank epsilon relation. -/
theorem unequal_factor (hnr : n < r)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {e : ℂˣ × ℤ} (h : IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e) :
    IsUnequalRankEpsilonFactor hnr q ψ abv ν
      (Langlands.twist (χ₁.comp determinant) π)
      (Langlands.twist (χ₂.comp determinant) σ)
      (e.1 * spectralShiftUnit q hq u ^ e.2, e.2) := by
  obtain ⟨hμ, ⟨L, hL⟩, ⟨L', hL'⟩, hall⟩ := h
  refine ⟨hμ, ⟨UnramifiedGammaTwist.functional χ₁ π L, hL⟩,
    ⟨UnramifiedGammaTwist.functional χ₂ σ L', hL'⟩, ?_⟩
  intro hinv μ hμc K K' hK hK'
  let L₀ := untwistFunctional _ _ (χ₁.comp determinant)
    (determinantCharacter_unipotent χ₁) π K
  let L₀' := untwistFunctional _ _ (χ₂.comp determinant)
    (determinantCharacter_unipotent χ₂) σ K'
  exact unequal_equation ψ abv χ₁ χ₂ u h₁ h₂ hprod hnr q hq μ ν π σ L₀ L₀'
    (@hall hinv μ hμc L₀ L₀' hK hK')

include h₁ h₂ hprod in
/-- Transport of the ordered-pair epsilon relation under two determinant
characters whose product is the supplied absolute-value power. -/
theorem pair_factor
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {e : ℂˣ × ℤ} (h : IsPairEpsilonFactor q ψ abv ν π σ e) :
    IsPairEpsilonFactor q ψ abv ν
      (Langlands.twist (χ₁.comp determinant) π)
      (Langlands.twist (χ₂.comp determinant) σ)
      (e.1 * spectralShiftUnit q hq u ^ e.2, e.2) := by
  by_cases hnr : n < r
  · rw [isPairEpsilonFactor_of_lt hnr] at h ⊢
    exact unequal_factor q hq ψ abv ν χ₁ χ₂ u h₁ h₂ hprod hnr π σ h
  · by_cases hrn : r = n
    · subst r
      rw [isPairEpsilonFactor_self] at h ⊢
      exact equal_factor q hq ψ abv ν χ₁ χ₂ u h₁ h₂ hprod π σ h
    · exact False.elim ((not_isPairEpsilonFactor_of_lt (by omega)) h)

omit h₁ h₂ hprod in
/-- Specializing one character to the trivial character gives both twist
positions. -/
theorem pair_both (χ : Fˣ →* ℂˣ)
    (hχ : ∀ x : Fˣ, (χ x : ℂ) = (abv (x : F) : ℂ) ^ u)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {e : ℂˣ × ℤ} (h : IsPairEpsilonFactor q ψ abv ν π σ e) :
    IsPairEpsilonFactor q ψ abv ν π (Langlands.twist (χ.comp determinant) σ)
        (e.1 * spectralShiftUnit q hq u ^ e.2, e.2) ∧
      IsPairEpsilonFactor q ψ abv ν (Langlands.twist (χ.comp determinant) π) σ
        (e.1 * spectralShiftUnit q hq u ^ e.2, e.2) := by
  have hsign := UnramifiedGammaTwist.character_neg_one abv χ u hχ
  constructor
  · simpa only [MonoidHom.one_comp, Langlands.twist_one] using
      pair_factor q hq ψ abv ν (1 : Fˣ →* ℂˣ) χ u (by simp) hsign
        (fun x => by simpa only [MonoidHom.one_apply, Units.val_one, one_mul] using hχ x)
        π σ h
  · simpa only [MonoidHom.one_comp, Langlands.twist_one] using
      pair_factor q hq ψ abv ν χ (1 : Fˣ →* ℂˣ) u hsign (by simp)
        (fun x => by simpa only [MonoidHom.one_apply, Units.val_one, mul_one] using hχ x)
        π σ h

end Relations

section PadicTransport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (u : ℂ) (χ : F.Carrierˣ →* ℂˣ)
  (hχ : ∀ x : F.Carrierˣ,
    (χ x : ℂ) = (F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℂ) ^ u)

/-- The transported epsilon value at the residue cardinality of `F`. -/
abbrev shiftedValue (e : ℂˣ × ℤ) : ℂˣ × ℤ :=
  (e.1 * spectralShiftUnit F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one u ^ e.2, e.2)

include hχ in
/-- The canonical p-adic specialization of the ordered-pair transport. -/
theorem padic_pair_both {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    {e : ℂˣ × ℤ} (h : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    IsPadicPairEpsilonFactor F ψ ν π (Langlands.twist (χ.comp determinant) σ)
        (shiftedValue F u e) ∧
      IsPadicPairEpsilonFactor F ψ ν (Langlands.twist (χ.comp determinant) π) σ
        (shiftedValue F u e) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  exact pair_both F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) ν u χ hχ π σ h

include hχ in
/-- Reading the larger rank first covers either rank order and exchanges the
two twist positions in the reversed branch. -/
theorem padic_symmetric_both {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    {e : ℂˣ × ℤ} (h : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) :
    IsPadicSymmetricEpsilonFactor F ψ ν π (Langlands.twist (χ.comp determinant) σ)
        (shiftedValue F u e) ∧
      IsPadicSymmetricEpsilonFactor F ψ ν (Langlands.twist (χ.comp determinant) π) σ
        (shiftedValue F u e) := by
  unfold IsPadicSymmetricEpsilonFactor at h ⊢
  split_ifs at h ⊢ with hnr
  · exact padic_pair_both F ψ ν u χ hχ π σ h
  · exact (padic_pair_both F ψ ν u χ hχ σ π h).symm

/-- The coefficient of the transported value is `c q^(-mu)`. -/
theorem shiftedValue_fst (e : ℂˣ × ℤ) :
    ((shiftedValue F u e).1 : ℂ) =
      (e.1 : ℂ) *
        (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-((e.2 : ℂ) * u)) := by
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, coe_spectralShiftUnit,
    spectralPoint]
  rw [show -((e.2 : ℂ) * u) = (e.2 : ℂ) * -u by ring, Complex.cpow_int_mul]

end PadicTransport

end UnramifiedEpsilonTwist

/-- Henniart 1993, §4.4: twisting either member of a pair by `|det|^u` shifts
its epsilon factor from `s` to `s + u`. -/
theorem unramifiedTwistEpsilon : UnramifiedTwistEpsilonStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t V _ _ W _ _ π σ u χ hχ e h
  obtain ⟨h₁, h₂⟩ := UnramifiedEpsilonTwist.padic_symmetric_both F ψ ν.val u χ hχ π σ h
  exact ⟨UnramifiedEpsilonTwist.shiftedValue F u e, rfl,
    UnramifiedEpsilonTwist.shiftedValue_fst F u e, h₁, h₂⟩

end Langlands.RankinSelberg
