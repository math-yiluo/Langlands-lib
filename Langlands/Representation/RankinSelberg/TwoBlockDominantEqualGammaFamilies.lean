import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualLContinuation
import Langlands.Representation.RankinSelberg.EqualRankSwapTransport
import Langlands.Representation.RankinSelberg.RationalGammaComparison

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open ParameterSpecialization

universe uF uV uW

section Translation

variable {K : Type uF} [Field K] [TopologicalSpace K]
  {n : ℕ} (ψ : UnitaryAdditiveCharacter K)

/-- The fixed right translate of an inverse-character coefficient function. -/
def translateInverseWhittaker (f : InverseWhittakerFunctions ψ n)
    (a : GeneralLinear (n + 1) K) : InverseWhittakerFunctions ψ n :=
  ⟨fun g => f.val (g * a), by
    intro u g
    change f.val ((u.val * g) * a) = (inverseStandardCharacter ψ n u : ℂ) * f.val (g * a)
    rw [mul_assoc, f.property]⟩

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (τ : Representation ℂ (GeneralLinear (n + 1) K) W)
  (ell : glInverseFunctionals ψ n τ)

theorem translateInverseWhittaker_coefficient (v : W) (a : GeneralLinear (n + 1) K) :
    translateInverseWhittaker ψ (coefficientMap τ ell v) a =
      coefficientMap τ ell (τ a v) := by
  apply Subtype.ext
  funext g
  change ell.val (τ (g * a) v) = ell.val (τ g (τ a v))
  rw [map_mul, Module.End.mul_apply]

/-- Translating by the fixed central matrix absorbs the actual model sign. -/
theorem translateInverseWhittaker_central_apply
    {ζ : ℂˣ} (hζ : HasModelMinusOneScalar τ ell ζ)
    (f : (coefficientModel τ ell).toSubmodule) (g : GeneralLinear (n + 1) K) :
    (translateInverseWhittaker ψ f.val ((-1) ^ n)).val g =
      (ζ : ℂ) ^ n * f.val.val g := by
  have hc : Commute (-1 : GeneralLinear (n + 1) K) g := by
    apply Units.ext
    simp
  change f.val.val (g * (-1) ^ n) = _
  rw [← (hc.pow_left n).eq, hζ.pow_apply]

variable [MeasurableSpace (LeftUnipotentQuotient n K)]
  (μ : Measure (LeftUnipotentQuotient n K)) (abv : AbsoluteValue K ℝ)

/-- The central translate scales the actual integral, including zero and
nonintegrable tests under the total-integral convention. -/
theorem equalRankIntegral_central_translate
    {ζ : ℂˣ} (hζ : HasModelMinusOneScalar τ ell ζ)
    (f : WhittakerFunctions ψ n) (f' : (coefficientModel τ ell).toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → K)) (s : ℂ) :
    equalRankIntegral ψ abv μ f
        (translateInverseWhittaker ψ f'.val ((-1) ^ n)) Φ s =
      (ζ : ℂ) ^ n * equalRankIntegral ψ abv μ f f'.val Φ s := by
  have heq : equalRankIntegrand ψ abv f
      (translateInverseWhittaker ψ f'.val ((-1) ^ n)) Φ s =
      fun q => (ζ : ℂ) ^ n * equalRankIntegrand ψ abv f f'.val Φ s q := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [equalRankIntegrand_mk,
        translateInverseWhittaker_central_apply ψ τ ell hζ f' g]
      ring
  unfold equalRankIntegral
  rw [heq, integral_const_mul]

end Translation

section ScalarEquation

open LocalFactor

/-- Absorb a model sign into the primal rational continuation. -/
theorem gammaFunctionalEquation_absorb_scalar
    {q : ℕ} (hq : 1 < q) {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    {ζ : ℂˣ} {e : ℕ} {G R Rd : RationalFunctions} :
    GammaFunctionalEquation q ζ e G R Rd ↔
      GammaFunctionalEquation q 1 e G (RatFunc.C ((ζ : ℂ) ^ e) * R) Rd := by
  rw [RationalGammaComparison.gammaFunctionalEquation_iff_rational_identity hq hδ,
    RationalGammaComparison.gammaFunctionalEquation_iff_rational_identity hq hδ]
  simp only [Units.val_one, one_pow, map_one, one_mul, mul_left_comm G]

end ScalarEquation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalGammaFamiliesTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalGammaFamiliesValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalGammaFamiliesLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalGammaFamiliesT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalGammaFamiliesMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalGammaFamiliesBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalGammaFamiliesGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalGammaFamiliesGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaFamiliesUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalGammaFamiliesUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaFamiliesQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalGammaFamiliesQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T

section Entire

variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
  (U : ℂ → InverseWhittakerFunctions ψ n)
  (K : Subgroup (GeneralLinear (n + 1) F.Carrier))
  (hKo : IsOpen (K : Set (GeneralLinear (n + 1) F.Carrier)))
  (hKc : IsCompact (K : Set (GeneralLinear (n + 1) F.Carrier)))
  (hK : ∀ (u : ℂ) (g : GeneralLinear (n + 1) F.Carrier) (k : K),
    (U u).val (g * k) = (U u).val g)
  (hU : ∀ (g : GeneralLinear (n + 1) F.Carrier) (u : ℂ),
    AnalyticAt ℂ (fun z => (U z).val g) u)

include K hKo hKc hK hU

/-- A fixed translate retains a common compact open level and entire values. -/
theorem inverseWhittaker_translate_level_entire (a : GeneralLinear (n + 1) F.Carrier) :
    (∃ L : Subgroup (GeneralLinear (n + 1) F.Carrier),
      IsOpen (L : Set (GeneralLinear (n + 1) F.Carrier)) ∧
      IsCompact (L : Set (GeneralLinear (n + 1) F.Carrier)) ∧
      ∀ (u : ℂ) (g : GeneralLinear (n + 1) F.Carrier) (k : L),
        (translateInverseWhittaker ψ (U u) a).val (g * k) =
          (translateInverseWhittaker ψ (U u) a).val g) ∧
    ∀ (g : GeneralLinear (n + 1) F.Carrier) (u : ℂ),
      AnalyticAt ℂ (fun z => (translateInverseWhittaker ψ (U z) a).val g) u := by
  let e : GeneralLinear (n + 1) F.Carrier ≃ₜ GeneralLinear (n + 1) F.Carrier :=
    (Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight a)
  let L := K.comap (MulAut.conj a⁻¹).toMonoidHom
  have hL : (L : Set (GeneralLinear (n + 1) F.Carrier)) = e ⁻¹' K := by
    ext k
    simp [L, e]
  refine ⟨⟨L, ?_, ?_, ?_⟩, fun g u => hU (g * a) u⟩
  · rw [hL]
    exact e.isOpen_preimage.mpr hKo
  · rw [hL]
    exact e.isCompact_preimage.mpr hKc
  · intro u g k
    have hk : a⁻¹ * k.val * a ∈ K := by
      have hk' := k.property
      change a⁻¹ * k.val * (a⁻¹)⁻¹ ∈ K at hk'
      simpa only [inv_inv] using hk'
    change (U u).val ((g * k.val) * a) = (U u).val (g * a)
    have heq : (g * k.val) * a = (g * a) * (a⁻¹ * k.val * a) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [heq]
    exact hK u (g * a) ⟨_, hk⟩

/-- The actual second dual pulls the common level back by inverse transpose. -/
theorem inverseWhittaker_secondDual_level_entire :
    (∃ L : Subgroup (GeneralLinear (n + 1) F.Carrier),
      IsOpen (L : Set (GeneralLinear (n + 1) F.Carrier)) ∧
      IsCompact (L : Set (GeneralLinear (n + 1) F.Carrier)) ∧
      ∀ (u : ℂ) (g : GeneralLinear (n + 1) F.Carrier) (k : L),
        (secondDualFunction ψ n (U u)).val (g * k) =
          (secondDualFunction ψ n (U u)).val g) ∧
    ∀ (g : GeneralLinear (n + 1) F.Carrier) (u : ℂ),
      AnalyticAt ℂ (fun z => (secondDualFunction ψ n (U z)).val g) u := by
  let e := inverseTransposeContinuous (n + 1) F.Carrier
  let L := K.comap e.toMonoidHom
  refine ⟨⟨L, e.toHomeomorph.isOpen_preimage.mpr hKo,
    e.toHomeomorph.isCompact_preimage.mpr hKc, ?_⟩, fun g u => hU _ u⟩
  intro u g k
  change (U u).val (weylLong (n + 1) F.Carrier *
      inverseTranspose (n + 1) F.Carrier (g * k.val)) =
    (U u).val (weylLong (n + 1) F.Carrier *
      inverseTranspose (n + 1) F.Carrier g)
  rw [map_mul, ← mul_assoc]
  exact hK u _ ⟨e k.val, k.property⟩

variable (μ : Measure (LeftUnipotentQuotient n F.Carrier)) [IsFiniteMeasureOnCompacts μ]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
  (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
  (lambda : glFunctionals ψ n π) (f : (coefficientModel π lambda).toSubmodule)
  (Φ Φhat : SchwartzBruhat (Fin (n + 1) → F.Carrier))

include hπ

/-- Both literal slice families used for sign-absorbed gamma continuation
are entire; no parameter-dependent scalar is divided out. -/
theorem equalGammaSliceFamilies_entire :
    EntireCoefficientFamily (fun u =>
      equalRankSliceCoefficient T μ ψ f.val
        (translateInverseWhittaker ψ (U u) ((-1) ^ n)) Φ) ∧
    EntireCoefficientFamily (fun u =>
      equalRankSliceCoefficient T μ (ψ.scale (-1)) (firstDualFunction ψ n f.val)
        (secondDualFunction ψ n (U u)) Φhat) := by
  obtain ⟨⟨L, hLo, -, hL⟩, hUa⟩ :=
    inverseWhittaker_translate_level_entire F ψ U K hKo hKc hK hU ((-1) ^ n)
  obtain ⟨⟨Ld, hLdo, -, hLd⟩, hUda⟩ :=
    inverseWhittaker_secondDual_level_entire F ψ U K hKo hKc hK hU
  exact ⟨(equalRankEntireSliceData F ψ μ π lambda f Φ
      (fun u => translateInverseWhittaker ψ (U u) ((-1) ^ n)) hπ.1.1
      L hLo hL hUa).2,
    (equalRankEntireSliceData F (ψ.scale (-1)) μ (inverseTransposePullback π)
      (firstDualFunctional ψ π lambda) (firstDualModelMap ψ π lambda f) Φhat
      (fun u => secondDualFunction ψ n (U u))
      (isOfWhittakerType_firstDual ψ π hπ).1.1 Ld hLdo hLd hUda).2⟩

end Entire

end Langlands.RankinSelberg.DominantRankTransport
