import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.EqualRankSwapTransport
import Langlands.Representation.RankinSelberg.RationalGammaComparison
import Langlands.Representation.RankinSelberg.UnequalRankComplementaryConjugationProof

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration LocalFactor
open UnequalRankComplementaryConjugationProof

universe uF uV uW

section Matrix

variable {F : Type uF} [Field F] {n r : ℕ} (hnr : n < r)

theorem blockWeylAt_mul_self :
    blockWeylAt (F := F) n r hnr * blockWeylAt n r hnr = 1 := by
  rw [blockWeylAt_eq, ← map_mul]
  have hperm : tailRevPerm n r * tailRevPerm n r = 1 := by
    apply Equiv.ext
    intro i
    exact tailRev_involutive n r i
  rw [hperm, map_one]

theorem inverseTranspose_blockWeylAt :
    inverseTranspose (r + 1) F (blockWeylAt n r hnr) = blockWeylAt n r hnr := by
  rw [blockWeylAt_eq, inverseTranspose_permutation]

theorem inverseTranspose_neg (m : ℕ) (g : Langlands.GeneralLinear m F) :
    inverseTranspose m F (-g) = -inverseTranspose m F g := by
  apply Units.ext
  simp [inverseTranspose_coe]

end Matrix

section Functions

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n r : ℕ} (hnr : n < r) (ψ : UnitaryAdditiveCharacter F)

theorem translatedFirstDualFunction_twice
    (f : WhittakerFunctions ψ r) (g : Langlands.GeneralLinear (r + 1) F) :
    (translateWhittaker ((ψ.scale (-1)).scale (-1)) r
      (firstDualFunction (ψ.scale (-1)) r
        (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f)
          (blockWeylAt n r hnr))) (blockWeylAt n r hnr)).val g = f.val g := by
  simp only [translateWhittaker_apply, firstDualFunction_apply, map_mul,
    inverseTranspose_weylLong, inverseTranspose_blockWeylAt,
    inverseTranspose_involutive]
  rw [← mul_assoc, ← mul_assoc, weylLong_mul_self, one_mul, mul_assoc,
    blockWeylAt_mul_self, mul_one]

theorem secondDualFunction_twice
    (f : InverseWhittakerFunctions ψ n) (g : Langlands.GeneralLinear (n + 1) F) :
    (secondDualFunction (ψ.scale (-1)) n (secondDualFunction ψ n f)).val g = f.val g := by
  change f.val (weylInverseTranspose (n + 1) F (weylInverseTranspose (n + 1) F g)) = _
  rw [weylInverseTranspose_involutive]

end Functions

section Integrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

omit [IsTopologicalRing F] in
theorem unequalRankIntegralAt_congr_raw
    (j k : ℕ) (hr : r = n + (j + k + 1))
    (ψ χ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (f : WhittakerFunctions ψ r) (f' : InverseWhittakerFunctions ψ n)
    (g : WhittakerFunctions χ r) (g' : InverseWhittakerFunctions χ n)
    (hf : f.val = g.val) (hf' : f'.val = g'.val) :
    unequalRankIntegralAt j k hr ψ abv μ ν f f' =
      unequalRankIntegralAt j k hr χ abv μ ν g g' := by
  subst r
  funext s
  apply integral_congr_ae
  filter_upwards [] with q
  apply integral_congr_ae
  filter_upwards [] with x
  induction q using Quotient.inductionOn with
  | h a => simp only [unequalRankIntegrand_mk, hf, hf']

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (hnr : n < r) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)

theorem dualUnequalRankModelIntegralAt_twice
    (j k : ℕ) (hr : r = n + (j + k + 1))
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule) :
    dualUnequalRankModelIntegralAt hnr k j (by omega) (ψ.scale (-1)) abv μ ν
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
      (translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr) f)
      (secondDualModelMap ψ σ ℓ' f') =
    unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
      f.val f'.val := by
  unfold dualUnequalRankModelIntegralAt
  apply unequalRankIntegralAt_congr_raw
  · funext g
    exact translatedFirstDualFunction_twice hnr ψ f.val g
  · funext g
    exact secondDualFunction_twice ψ f'.val g

omit [MeasurableSpace F] [MeasurableSpace (LeftUnipotentQuotient n F)] in
theorem hasModelMinusOneScalar_secondDual {ζ : ℂˣ}
    (hζ : HasModelMinusOneScalar σ ℓ' ζ) :
    HasModelMinusOneScalar (inverseTransposePullback σ) (secondDualFunctional ψ σ ℓ') ζ := by
  intro g a
  obtain ⟨f, rfl⟩ := (secondDualModelMap_bijective ψ σ ℓ').surjective g
  change f.val.val (weylLong (n + 1) F *
      inverseTranspose (n + 1) F ((-1) * a)) =
    (ζ : ℂ) * f.val.val (weylLong (n + 1) F * inverseTranspose (n + 1) F a)
  have heq : weylLong (n + 1) F * inverseTranspose (n + 1) F ((-1) * a) =
      (-1) * (weylLong (n + 1) F * inverseTranspose (n + 1) F a) := by
    simp only [neg_one_mul, inverseTranspose_neg, mul_neg]
  rw [heq, hζ]

end Integrals

section Rational

open RationalGammaComparison

theorem gammaFunctionalEquation_reflection_mul
    {q : ℕ} (hq : 1 < q) {δ ζ : ℂˣ}
    (hδ : (δ : ℂ) = (q : ℂ)⁻¹) {e : ℕ}
    (hζ : ζ ^ 2 = 1) {G GD R RD : RationalFunctions}
    (hR : R ≠ 0) (h : GammaFunctionalEquation q ζ e G R RD)
    (hD : GammaFunctionalEquation q ζ e GD RD R) :
    G * RationalReflection.subst δ GD = 1 := by
  have h₁ := (gammaFunctionalEquation_iff_rational_identity hq hδ).mp h
  have h₂ := congrArg (RationalReflection.subst δ)
    ((gammaFunctionalEquation_iff_rational_identity hq hδ).mp hD)
  have hsC : ∀ z : ℂ, RationalReflection.subst δ (RatFunc.C z) = RatFunc.C z :=
    fun z => (RationalReflection.subst δ).commutes z
  simp only [RationalReflection.subst_subst, map_mul, hsC] at h₂
  rw [h₁] at h₂
  have hc : RatFunc.C ((ζ : ℂ) ^ e) * RatFunc.C ((ζ : ℂ) ^ e) = 1 := by
    rw [← map_mul, ← mul_pow]
    have hz : (ζ : ℂ) * (ζ : ℂ) = 1 := by
      simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val hζ
    rw [hz, one_pow, map_one]
  apply mul_right_cancel₀ hR
  calc
    (G * RationalReflection.subst δ GD) * R =
        (RatFunc.C ((ζ : ℂ) ^ e) * RatFunc.C ((ζ : ℂ) ^ e)) *
          (RationalReflection.subst δ GD * (G * R)) := by rw [hc]; ring
    _ = R := by linear_combination -h₂
    _ = 1 * R := (one_mul R).symm

end Rational

section Gamma

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {hnr : n < r} {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

theorem unequalRankGammaEquation_reflection_mul
    (hq : 1 < q) {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hℓ' : ℓ'.val ≠ 0) {G GD : RationalFunctions}
    (hG : UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G)
    (hGD : UnequalRankGammaEquation hnr q (ψ.scale (-1)) abv μ ν
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ') GD) :
    G * RationalReflection.subst δ GD = 1 := by
  obtain ⟨ζ, hζ, hall⟩ := hG
  obtain ⟨ζD, hζD, hallD⟩ := hGD
  obtain rfl := (hasModelMinusOneScalar_secondDual ψ σ ℓ' hζ).unique
    (secondDualFunctional_ne_zero ψ σ hℓ') hζD
  have hr : r = n + (0 + (r - n - 1) + 1) := by omega
  obtain ⟨⟨R, hRmem, hR0⟩, hFE⟩ := hall 0 (r - n - 1) hr
  rw [unequalRankValuesAt_eq_set] at hRmem
  obtain ⟨f, f', hR⟩ := hRmem
  obtain ⟨R₁, RD, hR₁, hRD, h₁⟩ := hFE f f'
  obtain rfl := hR.unique hq hR₁
  obtain ⟨RD₁, R₂, hRD₁, hR₂, h₂⟩ := (hallD (r - n - 1) 0 (by omega)).2
    (translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr) f)
    (secondDualModelMap ψ σ ℓ' f')
  have hRD₁' : HasRationalContinuation q
      (dualUnequalRankModelIntegralAt hnr 0 (r - n - 1) hr ψ abv μ ν π σ ℓ ℓ' f f')
      RD₁ := hRD₁
  obtain rfl := hRD.unique hq hRD₁'
  rw [dualUnequalRankModelIntegralAt_twice hnr ψ abv μ ν π σ ℓ ℓ'
    0 (r - n - 1) hr f f'] at hR₂
  obtain rfl := hR.unique hq hR₂
  exact gammaFunctionalEquation_reflection_mul hq hδ (hζ.sq_eq_one hℓ') hR0 h₁ h₂

/-- The reflection law for all gamma factors certified on these actual models. -/
def UnequalRankGammaDualReflectionLaw
    (hnr : n < r) (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (δ : ℂˣ) : Prop :=
  ∀ G GD : RationalFunctions,
    UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G →
    UnequalRankGammaEquation hnr q (ψ.scale (-1)) abv μ ν
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ') GD →
    G * RationalReflection.subst δ GD = 1

theorem unequalRankGammaDualReflectionLaw
    (hq : 1 < q) {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹) (hℓ' : ℓ'.val ≠ 0) :
    UnequalRankGammaDualReflectionLaw hnr q ψ abv μ ν π σ ℓ ℓ' δ := by
  intro G GD hG hGD
  exact unequalRankGammaEquation_reflection_mul hq hδ hℓ' hG hGD

end Gamma

end Langlands.RankinSelberg.DominantRankTransport
