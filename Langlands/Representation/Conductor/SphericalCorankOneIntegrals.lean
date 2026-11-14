import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Corank-one integrals as the zero blocks of the unequal-rank family

Over an arbitrary field, the corank-one integral of a pair of ranks `n + 2 > n + 1` is the
unequal-rank integral with blocks `j = k = 0`, its absolute convergence is the
convergence of that block, and the transformed zero block is the corank-one integral of
the two dual functions. Consequently a gamma factor of the pair yields the gamma
functional equation for the corank-one integrals of any two model functions.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCorankOne

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open Langlands.RankinSelberg

universe uF uV uW

section Integrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)

omit [IsTopologicalRing F] in
/-- The corank-one integral is the unequal-rank integral of the zero blocks. -/
theorem corankOneIntegral_eq_unequalRankIntegralAt
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n) :
    corankOneIntegral ψ abv μ W W' =
      unequalRankIntegralAt 0 0 rfl ψ abv μ (rectangularMeasure ν 0 (n + 1)) W W' := by
  funext s
  change corankOneIntegral ψ abv μ W W' s =
    unequalRankIntegral ψ abv 0 0 μ (rectangularMeasure ν 0 (n + 1)) W W' s
  simp only [unequalRankIntegral, rectangularMeasure_zero_rows, integral_dirac,
    unequalRankIntegrand_zero_zero, corankOneIntegral]

omit [IsTopologicalRing F] in
/-- Absolute convergence of the corank-one integral is that of the zero blocks. -/
theorem corankOneConverges_iff_unequalRankConverges
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    CorankOneConverges ψ abv μ W W' s ↔
      UnequalRankConverges ψ abv 0 0 μ (rectangularMeasure ν 0 (n + 1)) W W' s := by
  unfold UnequalRankConverges
  rw [rectangularMeasure_zero_rows]
  constructor
  · intro h
    have hc : Integrable (fun _ : Matrix (Fin 0) (Fin (n + 1)) F => (1 : ℂ))
        (Measure.dirac 0) := integrable_const 1
    apply (h.mul_prod hc).congr
    filter_upwards [] with qx
    rw [mul_one, unequalRankIntegrand_zero_zero]
  · intro h
    have h0 := h.integral_prod_left
    simp only [integral_dirac, unequalRankIntegrand_zero_zero] at h0
    exact h0

omit [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [MeasurableSpace (LeftUnipotentQuotient n F)] in
/-- The block Weyl representative is the identity in corank one. -/
theorem blockWeylAt_succ_eq_one :
    blockWeylAt (F := F) n (n + 1) (Nat.lt_succ_self n) = 1 := by
  have hw : weylLong (n + 1 - n) F = 1 := by
    have hdim : n + 1 - n = 1 := by omega
    rw [hdim, RankOneGammaTwist.weylLong_one]
  unfold blockWeylAt
  rw [hw]
  change GeneralLinear.reindex _ (blockSum 1) = 1
  rw [map_one, map_one]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- In corank one the transformed zero-block integral is the corank-one integral of the
two dual functions. -/
theorem dualUnequalRankModelIntegralAt_eq_corankOneIntegral
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1 + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ (n + 1) π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    dualUnequalRankModelIntegralAt (Nat.lt_succ_self n) 0 0 rfl ψ abv μ ν π σ ℓ ℓ' f f' =
      corankOneIntegral (ψ.scale (-1)) abv μ (firstDualFunction ψ (n + 1) f.val)
        (secondDualFunction ψ n f'.val) := by
  unfold dualUnequalRankModelIntegralAt
  rw [blockWeylAt_succ_eq_one]
  have ht : translateWhittaker (ψ.scale (-1)) (n + 1)
      (firstDualFunction ψ (n + 1) f.val) 1 = firstDualFunction ψ (n + 1) f.val := by
    apply Subtype.ext
    funext g
    exact congrArg (firstDualFunction ψ (n + 1) f.val).val (mul_one g)
  rw [ht]
  exact (corankOneIntegral_eq_unequalRankIntegralAt (ψ.scale (-1)) abv μ ν _ _).symm

end Integrals

section Gamma

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A gamma factor `G` of a pair of ranks `n + 2 > n + 1` gives, for every compatible
quotient measure, every pair of nonzero functionals and every pair of model functions,
the gamma functional equation between the corank-one integral and the corank-one integral
of the two dual functions, with the model's minus-one scalar `ζ` and exponent `n + 1`. -/
theorem corankOne_gammaFunctionalEquation {q : ℕ} {ψ : UnitaryAdditiveCharacter F}
    {abv : AbsoluteValue F ℝ} {ν : AdditiveHaarMeasure F}
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1 + 1) F) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W} {G : RationalFunctions}
    (hG : IsPairGammaFactor q ψ abv ν π σ G)
    [Measure.IsMulRightInvariant (unipotentHaar F n)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0)
    (ℓ' : glInverseFunctionals ψ n σ) (hℓ' : ℓ'.val ≠ 0)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    ∃ ζ : ℂˣ, HasModelMinusOneScalar σ ℓ' ζ ∧
      ∃ R Rdual : RationalFunctions,
        HasRationalContinuation q (corankOneIntegral ψ abv μ f.val f'.val) R ∧
        HasRationalContinuation q
          (corankOneIntegral (ψ.scale (-1)) abv μ (firstDualFunction ψ (n + 1) f.val)
            (secondDualFunction ψ n f'.val)) Rdual ∧
        GammaFunctionalEquation q ζ (n + 1) G R Rdual := by
  have hnr : n < n + 1 := Nat.lt_succ_self n
  rw [isPairGammaFactor_of_lt hnr] at hG
  obtain ⟨-, -, -, hall⟩ := hG
  obtain ⟨ζ, hζ, hFE⟩ := hall μ hμ ℓ ℓ' hℓ hℓ'
  obtain ⟨-, hT⟩ := hFE 0 0 rfl
  obtain ⟨R, Rd, hR, hRd, hN⟩ := hT f f'
  refine ⟨ζ, hζ, R, Rd, ?_, ?_, hN⟩
  · rw [corankOneIntegral_eq_unequalRankIntegralAt ψ abv μ ν]
    exact hR
  · rw [← dualUnequalRankModelIntegralAt_eq_corankOneIntegral ψ abv μ ν π σ ℓ ℓ' f f']
    exact hRd

end Gamma

end Langlands.Conductor.SphericalCorankOne
