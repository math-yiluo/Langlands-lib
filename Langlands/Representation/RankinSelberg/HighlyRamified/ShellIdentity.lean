import Langlands.Representation.RankinSelberg.HighlyRamified.DualShellIntegral
import Langlands.Representation.RankinSelberg.HighlyRamified.ForwardConstant
import Langlands.Representation.RankinSelberg.HighlyRamified.CorankShells
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof

/-!
# Shell identities for the twisted smeared test vector

Combining the dual evaluation `dual_shell_integral`, the functional equation with a monomial
gamma factor (`corankOne_eq_const_of_gamma_monomial`) and Laurent extraction on determinant
shells (`corankOne_shell_eq_of_const`): for a test vector `W''` of `τ`, the corank-one integrand
of the twisted smeared vector `Fbig` against `W''` at `s = 0` integrates to `0` over every
shell `ord det ≠ 0`, and to an explicit constant times `∫_(K⁰(f)) ω(k₀₀) W''(k) dk` over the
shell `ord det = 0`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear

universe uF uV uX

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance shellIdentityFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance shellIdentityValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance shellIdentityLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance shellIdentityFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance shellIdentityFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance shellIdentityGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance shellIdentityGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance shellIdentityUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance shellIdentityUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance shellIdentityQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance shellIdentityQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

variable {m : ℕ}

/-- Absolute convergence of the corank-one integral of model vectors on a right half-plane
(JPSS 1983, Theorem 2.7, published as `unequalRankAnalytic`). -/
theorem corankOne_integrable_of_whittakerType (ψ : UnitaryAdditiveCharacter F.Carrier)
    (η : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {Pi : Representation ℂ (GeneralLinear (m + 1 + 1) F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) X}
    (hPi : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) Pi)
    (hτ : IsOfWhittakerType m (inverseStandardCharacter ψ m) τ)
    (ℓ : glFunctionals ψ (m + 1) Pi) (hℓ : ℓ.val ≠ 0)
    (ℓ'' : glInverseFunctionals ψ m τ) (hℓ'' : ℓ''.val ≠ 0)
    (f : (coefficientModel Pi ℓ).toSubmodule) (W'' : (coefficientModel τ ℓ'').toSubmodule) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      Integrable (corankOneIntegrand ψ abv f.val W''.val s) (unipotentQuotientHaar F.Carrier m) := by
  have := unipotentHaar_isMulRightInvariant F.Carrier m
  have hA := unequalRankAnalytic F F.canonicalTopologicalData m 0 0 ψ
    (unipotentQuotientHaar F.Carrier m) (unipotentQuotientHaar_isCompatible F.Carrier m) η
    V X Pi τ hPi hτ ℓ ℓ'' hℓ hℓ''
  obtain ⟨a, ha⟩ := hA.1 f W''
  refine ⟨a, fun s hs => ?_⟩
  have h := (UnequalRankZeroRowAssembly.zero_row_converges_iff ψ abv 0
    (unipotentQuotientHaar F.Carrier m) η f.val W''.val s).mp (ha s hs)
  refine h.congr (Filter.Eventually.of_forall fun q => ?_)
  exact unequalRankIntegrand_zero_zero ψ abv f.val W''.val s 0 q

/-- The `s`-dependence of `dualShellConstant` for a uniformizer: it is the value at `0`
times `(q^(-s))^(-c(m+1))`. -/
theorem dualShellConstant_eq_mul (η : AdditiveHaarMeasure F.Carrier) (χ : F.Carrierˣ →* ℂˣ)
    (ϖ : F.Carrierˣ) (hϖ : F.canonicalTopologicalData.ord (ϖ : F.Carrier) = 1) (c : ℕ)
    (κ₁ ωτ s : ℂ) :
    dualShellConstant F η χ ϖ c m κ₁ ωτ s =
      dualShellConstant F η χ ϖ c m κ₁ ωτ 0 * spectralPoint qF s ^ (-((c * (m + 1) : ℕ) : ℤ)) := by
  set z := Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹ with hz
  have hne : ((abv (Matrix.det z.val) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact AbsoluteValue.ne_zero _ z.det_ne_zero
  have hw : determinantWeight abv z (s - 1 / 2) =
      determinantWeight abv z (0 - 1 / 2) * determinantWeight abv z s := by
    unfold determinantWeight
    rw [← Complex.cpow_add _ _ hne]
    ring_nf
  have hord : F.canonicalTopologicalData.ord (determinant z : F.Carrier) =
      -((c * (m + 1) : ℕ) : ℤ) := by
    rw [hz, determinant_scalar]
    have : (((ϖ ^ c)⁻¹ ^ (m + 1) : F.Carrierˣ) : F.Carrier) =
        (ϖ : F.Carrier) ^ (-((c * (m + 1) : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val, inv_pow, ← pow_mul]
    rw [this, F.canonicalTopologicalData.ord_zpow, hϖ, mul_one]
  unfold dualShellConstant
  rw [← hz, hw, determinantWeight_eq_spectral F z s, hord]
  ring

/-- The shell identities: for the twisted smeared vector `Fbig` of the Kirillov test vector and
any test vector `W''` of `τ`, the integral at `s = 0` of the corank-one integrand over the shell
`ord det = j` vanishes for `j ≠ 0`, and for `j = 0` it is
`(ζ^(m+1))⁻¹ C⁻¹ c_d q^(c(m+1))` with
`c_d = dualShellConstant(0) ω(-1)⁻¹ ∫_(K⁰(f)) ω(k₀₀) W''(k) dk`. -/
theorem shell_identity (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductorAt F ψ)
    (η ν : AdditiveHaarMeasure F.Carrier) (χ : F.Carrierˣ →* ℂˣ)
    {ω : F.Carrierˣ →* ℂˣ} {f c : ℕ} (hf : 0 < f) (hω : TrivialOnPrincipalUnits ω f)
    (ϖ : F.Carrierˣ) (hϖ : F.canonicalTopologicalData.ord (ϖ : F.Carrier) = 1)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer,
      InPow f ((ϖ : F.Carrier) ^ c * o))
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ y, dualWeight ω (ϖ : F.Carrier) c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m)
    (f' : InverseWhittakerFunctions ψ (m + 1)) (κ₁ : ℂ)
    (hsupp : ∀ B : GeneralLinear (m + 1) F.Carrier, f'.val (rankInclusion 1 B) ≠ 0 →
      ∃ u : upperUnipotent (m + 1) F.Carrier,
        IsIntegralMatrix (u.val * B * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)))
    (hval : ∀ k : GeneralLinear (m + 1) F.Carrier, IsIntegralMatrix k →
      f'.val (rankInclusion 1 (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)) =
        κ₁ * ((χ (determinant k) : ℂ))⁻¹)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {Pi : Representation ℂ (GeneralLinear (m + 1 + 1) F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) X}
    (hPi : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) Pi)
    (hτ : IsOfWhittakerType m (inverseStandardCharacter ψ m) τ)
    (ℓ : glFunctionals ψ (m + 1) Pi) (hℓ : ℓ.val ≠ 0)
    (ℓ'' : glInverseFunctionals ψ m τ) (hℓ'' : ℓ''.val ≠ 0)
    (Fbig : (coefficientModel Pi ℓ).toSubmodule)
    (hFbig : ∀ g, Fbig.val.val g = twistedSmear F ψ η χ ω (ϖ : F.Carrier) c f T f' g)
    (LF : OpenSubgroup (GeneralLinear (m + 1 + 1) F.Carrier))
    (hFL : ∀ g l, l ∈ LF → Fbig.val.val (g * l) = Fbig.val.val g)
    (W'' : (coefficientModel τ ℓ'').toSubmodule)
    (LW : OpenSubgroup (GeneralLinear (m + 1) F.Carrier))
    (hWL : ∀ g l, l ∈ LW → W''.val.val (g * l) = W''.val.val g) (ωτ : ℂ)
    (hWc : ∀ g, W''.val.val (g * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)) =
      ωτ * W''.val.val g)
    {G : RationalFunctions} (hG : IsPadicPairGammaFactor F ψ ν Pi τ G) (C : ℂˣ)
    (hGC : G = rationalEpsilonMonomial C ((c * (m + 1) : ℕ) : ℤ)) :
    ∃ ζ : ℂˣ, HasModelMinusOneScalar τ ℓ'' ζ ∧ ∀ j : ℤ,
      ∫ q in determinantSlice F.canonicalTopologicalData m j,
          corankOneIntegrand ψ abv Fbig.val W''.val 0 q ∂unipotentQuotientHaar F.Carrier m =
        if j = 0 then
          (((ζ : ℂ) ^ (m + 1)))⁻¹ * (C : ℂ)⁻¹ *
            (dualShellConstant F η χ ϖ c m κ₁ ωτ 0 * ((ω (-1) : ℂ))⁻¹ *
              ∫ k, (firstColumnOpenSubgroup F.Carrier m f :
                  Set (GeneralLinear (m + 1) F.Carrier)).indicator
                (fun k => (firstColumnCharacter ω hf k)⁻¹ * W''.val.val k) k
                ∂generalLinearHaar F.Carrier m) *
            (qF : ℂ) ^ (((c * (m + 1) : ℕ) : ℤ))
        else 0 := by
  set IK := ∫ k, (firstColumnOpenSubgroup F.Carrier m f :
      Set (GeneralLinear (m + 1) F.Carrier)).indicator
    (fun k => (firstColumnCharacter ω hf k)⁻¹ * W''.val.val k) k
    ∂generalLinearHaar F.Carrier m with hIK
  set cd := dualShellConstant F η χ ϖ c m κ₁ ωτ 0 * ((ω (-1) : ℂ))⁻¹ * IK with hcd
  have hJ : ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier m)
          (firstDualFunction ψ (m + 1) Fbig.val) (secondDualFunction ψ m W''.val) s =
        cd * (spectralPoint qF s) ^ (-(((c * (m + 1) : ℕ) : ℤ))) := by
    refine ⟨0, fun s _ => ?_⟩
    rw [dual_shell_integral F hψ hf hω hscale T hT hcov f' κ₁ hsupp hval Fbig.val hFbig LF hFL
      W''.val LW hWL ωτ hWc s, dualShellConstant_eq_mul F η χ ϖ hϖ c κ₁ ωτ s, hcd]
    ring
  obtain ⟨ζ, hζ, a, ha⟩ := corankOne_eq_const_of_gamma_monomial F ψ ν hG ℓ hℓ ℓ'' hℓ'' Fbig W''
    C _ hGC cd hJ
  obtain ⟨a', ha'⟩ := corankOne_integrable_of_whittakerType F ψ η hPi hτ ℓ hℓ ℓ'' hℓ'' Fbig W''
  refine ⟨ζ, hζ, fun j => ?_⟩
  have hshell := corankOne_shell_eq_of_const F ψ (unipotentQuotientHaar F.Carrier m) Fbig.val W''.val
    LF.toSubgroup LF.isOpen (fun g k => hFL g k k.property) (a' + 1)
    (ha' _ (by simp)) _ a ha j
  rw [hshell]

end Langlands.RankinSelberg.HighlyRamified
