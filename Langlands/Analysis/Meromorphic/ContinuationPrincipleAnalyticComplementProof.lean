import Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement
import Langlands.Analysis.Meromorphic.AnalyticComplementReduction
import Langlands.Analysis.SeveralComplex.Hartogs.Basic

/-! # Proof that the non-uniqueness locus is analytic

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, Theorem 3.3 (1): the
complement of the unique-solution locus is an analytic subset. The reduction
`isAnalyticSubset_compl_uniqueSolutionLocus_of_hartogs` proves this from Hartogs's theorem in
the diagonal form `HartogsDiagonal E`, and `differentiableOn_diag_of_separately` proves that
form for every finite-dimensional `E`. -/

noncomputable section
set_option autoImplicit false

universe uE uM uV uι uF

namespace Langlands.Analysis.Meromorphic

open Langlands.Analysis.SeveralComplex

/-- Hartogs's theorem in the diagonal form, for a finite-dimensional complex normed space. -/
theorem hartogsDiagonal_of_finiteDimensional (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] : HartogsDiagonal E :=
  fun _ _ hU h₁ h₂ => differentiableOn_diag_of_separately hU h₁ h₂

/-- **Bernstein–Lapid, Theorem 3.3 (1), analyticity of the non-uniqueness locus.** -/
theorem meromorphicContinuationAnalyticComplement :
    MeromorphicContinuationAnalyticComplementStatement.{uE, uM, uV, uι, uF} := by
  intro E _ _ _ M _ _ _ _ V _ _ _ _ _ _ _ _ _ ι F _ _ _ _ _ _ _ _ _ μ c hsys hft hint
  exact isAnalyticSubset_compl_uniqueSolutionLocus_of_hartogs
    (hartogsDiagonal_of_finiteDimensional E) hsys hft hint

end Langlands.Analysis.Meromorphic
