import Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement
/-!
# The ordinary two-block Jacquet integral as a nonzero Whittaker functional

JPSS 1983, Section (4.6), printed pages 410-411. For blocks `τ_1, τ_2` of Whittaker
type and the opposite real twists `σ_1 = τ_1 ⊗ α^(-u)`, `σ_2 = τ_2 ⊗ α^u`, the source
shows that for `u ≫ 0` the integral (4.6.2) converges for every section of the lower
induction `σ_u`, and that the resulting function of `g` belongs to `W(σ_u; ψ̄)`. This
module states the integral realization behind that claim: for `u` above one bound,
every section is absolutely integrable, and the ordinary integrals are the coefficients
`g ↦ J(σ_u(g) f)` of one nonzero inverse-character Whittaker functional `J` on the
actual induced representation. It proves nothing, and it does not compare `J` with
other Whittaker functionals of `σ_u`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

/-- JPSS 1983, Section (4.6), printed pages 410-411: for blocks `τ_1, τ_2` of full
standard Whittaker type and supplied nonzero inverse-character functionals `ℓ_1, ℓ_2`,
there is a real bound `C` such that for every real `u > C`, writing `σ_u` for the actual
lower induction of `(τ_1 |det|^(-u), τ_2 |det|^u)` and `μ` for the product of the
supplied self-dual Haar measure,

* the raw integrand of (4.6.2) of every section is absolutely integrable at every
  ambient element, and
* there is a nonzero `ψ⁻¹`-equivariant functional `J` on `σ_u` with
  `J(σ_u(g) f) = ∫ (ℓ_1 ⊗ ℓ_2)(f(u(x) g)) ψ(x_(m_0,0)) dμ(x)` for every section `f` and
  every `g`. -/
def TwoBlockOrdinaryJacquetFunctionalStatement.{uF, uW} : Prop :=
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
        (∀ f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u),
          Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell i).val)
            (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f) ∧
        ∃ J : glInverseFunctionals ψ t
            (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h (twoBlockOppositeTwistBlocks F m τ u)),
          J.val ≠ 0 ∧
          ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u))
            (g : Langlands.GeneralLinear (t + 1) F),
            J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h (twoBlockOppositeTwistBlocks F m τ u) g f) =
              Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
                (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g

end Langlands.AllField.RankinSelberg
