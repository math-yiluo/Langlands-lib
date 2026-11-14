import Langlands.Representation.RankinSelberg.AdjacentRankClearingKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAnalysis
import Langlands.AllField.Representation.RankinSelberg.UnramifiedTwistLFactorProof
/-! Actual unramified polynomial kernels with entire coefficients and fixed finite support. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.ParameterSpecialization
open Langlands.RankinSelberg.ParameterSpecialization
open Langlands.AllField.RankinSelberg.ParameterSpecialization
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnramifiedTwistLFactorStatement isPadicPairLPolynomial_unramified_of_transport isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_unramified_of_transport normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced unramifiedTwistLFactor unramifiedTwistLFactor_of_transport
open Langlands.AllField.RankinSelberg

open _root_.Polynomial
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped BigOperators

end Langlands.AllField.RankinSelberg.ParameterSpecialization

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding clearingKernelTopology symmetricLPolynomial_determinantComplexPower
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnramifiedTwistLFactorStatement isPadicPairLPolynomial_unramified_of_transport isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_unramified_of_transport normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced unramifiedTwistLFactor unramifiedTwistLFactor_of_transport
open Langlands.AllField.RankinSelberg

open _root_.Polynomial
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- The published complete unramified L transport applies to the literal
complex determinant-power block family, with no transport premise. -/
theorem symmetricLPolynomial_determinantComplexPower
    (ψ : UnitaryAdditiveCharacter F)
    (μ : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (GeneralLinear (n + 1) F) W)
    (u : ℂ) (P : Polynomial ℂ)
    (hP : IsPadicSymmetricLPolynomial F ψ μ.val π σ P) :
    IsPadicSymmetricLPolynomial F ψ μ.val π
      (Langlands.twist ((⟨⟩ : LocalFieldData F).determinantComplexPower (n + 1) u) σ)
      (P.comp (C (spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality u) * X)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let χ := T.unramifiedCharacter
    (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos u)
  have hχ : ∀ x : Fˣ,
      (χ x : ℂ) = (T.normalizedAbs (x : F) : ℂ) ^ u := by
    intro x
    simpa only [T.determinantNorm_scalar, pow_one, T.normalizedAbsUnits_coe,
      Langlands.LocalFieldData.determinantComplexPower,
      Langlands.LocalFieldData.determinantUnramifiedCharacter, MonoidHom.comp_apply,
      GeneralLinear.determinant, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] using
      T.determinantComplexPower_apply 1 u (GeneralLinear.scalar x)
  exact (unramifiedTwistLFactor F ψ μ r n π σ u χ hχ P hP).1

end Langlands.AllField.RankinSelberg.Padic
