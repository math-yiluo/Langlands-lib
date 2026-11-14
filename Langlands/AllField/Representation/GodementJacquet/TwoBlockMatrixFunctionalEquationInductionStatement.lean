import Langlands.Representation.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement
/-!
# Conditional two-block normalized matrix functional equation

The functional-equation part of Godement–Jacquet 1972, Theorem 3.4 (printed
pages 36–45), with two blocks, for split `GL` over a canonical p-adic field, in
the transpose Fourier convention of JPS 1979, printed page 177. The statement is
conditional: the block normalized matrix data are premises, and the blocks may
be reducible. This module only states the proposition.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding TwoBlockMatrixFunctionalEquationInductionStatement
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV

/-- Godement–Jacquet 1972, Theorem 3.4 (printed page 36), functional-equation
part, with two blocks. Let `σ i` be smooth admissible, not necessarily
irreducible, representations of `GL_(m i + 1)(F)` with scalar central
quasicharacters `ω i`, let `ψ` be a nontrivial additive character and `ν` a
Haar measure self-dual for `ψ`. If each block has normalized matrix
functional-equation data `(P i, PDual i, c i, a i)` for `ψ` and `ν`, then the
actual normalized induction of `(σ 0, σ 1)` to `GL_(t+1)(F)` has normalized
matrix functional-equation data with the products of the polynomials, the
product of the units and the sum of the exponents, for the same `ψ` and `ν`. -/
def TwoBlockMatrixFunctionalEquationInductionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      (V : Fin 2 → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (V i)),
      (∀ i, Langlands.IsSmooth (σ i)) →
      (∀ i, Langlands.IsAdmissible (σ i)) →
      ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F),
      IsSelfDual ψ ν →
      ∀ (ω : Fin 2 → Quasicharacter F),
      (∀ i, Classification.HasGLCentralCharacter F (m i + 1) (σ i)
        (ω i : Fˣ →* ℂˣ)) →
      ∀ (P PDual : Fin 2 → Polynomial ℂ) (c : Fin 2 → ℂˣ) (a : Fin 2 → ℤ),
      (∀ i, Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν (σ i)
        (P i) (PDual i) (c i) (a i)) →
      Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ)
        (∏ i, P i) (∏ i, PDual i) (∏ i, c i) (∑ i, a i)

end Langlands.AllField.GodementJacquet
