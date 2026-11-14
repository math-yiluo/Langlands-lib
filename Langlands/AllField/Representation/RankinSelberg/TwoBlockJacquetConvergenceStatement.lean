import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData
/-!
# Ordinary absolute convergence of the two-block Jacquet integral

JPSS 1983, Section (4.6), printed pages 410-411. For representations `τ_1, τ_2`
of Whittaker type of `GL_(m_0+1)(F)` and `GL_(m_1+1)(F)`, put
`σ_1 = τ_1 ⊗ α^(-u)` and `σ_2 = τ_2 ⊗ α^u` with `α = |det|` and `u` real. The
source asserts that for `u ≫ 0` the integral (4.6.2) of every section of the
lower induction `Ind(G_t, Q; σ_1 × σ_2)` converges. This module states that
assertion as ordinary absolute integrability of the published raw integrand
of `Langlands.Representation.RankinSelberg.TwoBlockJacquetData`, at every
ambient element, for every real `u` above one bound. It proves no convergence.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uW

section Family

variable (F : Type uF) [Field F] (m : Fin 2 → ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The blocks of JPSS (4.6) at the real parameter `u`: the first block is twisted
by `|det|^(-u)` and the second by `|det|^u`, on the same carriers. -/
abbrev twoBlockOppositeTwistBlocks [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)) (u : ℝ) :
    ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i) :=
  fun i => Langlands.twist
    ((⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
      (if i = 0 then -(u : ℂ) else (u : ℂ)))
    (τ i)

/-- The action of a twisted block is the scalar `|det g|^(∓u)` times the original action. -/
theorem twoBlockOppositeTwistBlocks_apply [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)) (u : ℝ)
    (i : Fin 2) (g : Langlands.GeneralLinear (m i + 1) F) :
    twoBlockOppositeTwistBlocks F m τ u i g =
      ((((⟨⟩ : LocalFieldData F).determinantNorm (m i + 1) g : NNReal) : ℝ) : ℂ) ^
          (if i = 0 then -(u : ℂ) else (u : ℂ)) • τ i g := by
  rw [← Langlands.LocalFieldData.determinantComplexPower_apply]
  rfl

/-- Every determinant power is trivial on the upper unipotent subgroup. -/
theorem determinantComplexPower_upperUnipotent [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n : ℕ) (s : ℂ)
    (x : upperUnipotent n F) :
    (⟨⟩ : LocalFieldData F).determinantComplexPower n s x.val = 1 := by
  apply Units.ext
  rw [Langlands.LocalFieldData.determinantComplexPower_apply,
    Langlands.LocalFieldData.determinantNorm_coe,
    show GeneralLinear.determinant x.val = 1 from Units.ext (unipotent_det x),
    Units.val_one, Langlands.LocalFieldData.normalizedAbs_one, Complex.ofReal_one,
    Complex.one_cpow, Units.val_one]

/-- The twisted blocks have full Whittaker type for a character exactly when the
original blocks do. -/
theorem twoBlockOppositeTwistBlocks_isOfWhittakerType_iff [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)) (u : ℝ)
    (i : Fin 2) (θ : upperUnipotent (m i + 1) F →* ℂˣ) :
    IsOfWhittakerType (m i) θ (twoBlockOppositeTwistBlocks F m τ u i) ↔
      IsOfWhittakerType (m i) θ (τ i) :=
  isOfWhittakerType_twist_iff θ _ (τ i)
    ((⟨⟩ : LocalFieldData F).isOpen_ker_determinantComplexPower (m i + 1) _)
    (determinantComplexPower_upperUnipotent F (m i + 1) _)

/-- A supplied inverse-character functional of `τ i` is, with the same linear map,
an inverse-character functional of the twisted block. -/
def twoBlockOppositeTwistFunctional [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)) (u : ℝ)
    (i : Fin 2) (ell : glInverseFunctionals ψ (m i) (τ i)) :
    glInverseFunctionals ψ (m i) (twoBlockOppositeTwistBlocks F m τ u i) :=
  twistFunctional (upperUnipotent (m i + 1) F) (inverseStandardCharacter ψ (m i))
    ((⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
      (if i = 0 then -(u : ℂ) else (u : ℂ)))
    (determinantComplexPower_upperUnipotent F (m i + 1) _) (τ i) ell

@[simp]
theorem twoBlockOppositeTwistFunctional_val [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)) (u : ℝ)
    (i : Fin 2) (ell : glInverseFunctionals ψ (m i) (τ i)) :
    (twoBlockOppositeTwistFunctional F m ψ τ u i ell).val = ell.val :=
  rfl

end Family

/-- JPSS 1983, Section (4.6), printed pages 410-411: for blocks `τ_1, τ_2` of full
standard Whittaker type and supplied nonzero inverse-character functionals
`ℓ_1, ℓ_2`, there is a real bound `C` such that for every real `u > C` and every
section `f` of the actual lower induction of `(τ_1 |det|^(-u), τ_2 |det|^u)`, the
raw integrand `x ↦ (ℓ_1 ⊗ ℓ_2)(f(u(x) g)) ψ(x_(m_0,0))` of (4.6.2) is integrable
for the product of the supplied self-dual Haar measure, at every ambient `g`. -/
def TwoBlockJacquetConvergenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
      (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i)),
      (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
      ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i), (∀ i, (ell i).val ≠ 0) →
      ∃ C : ℝ, ∀ u : ℝ, C < u →
        ∀ f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u),
          Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell i).val)
            (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f

end Langlands.AllField.RankinSelberg
