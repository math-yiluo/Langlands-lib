import Langlands.Global.RankinSelberg.RealPlaceContragredientPairLProof
import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProof
import Langlands.Global.RankinSelberg.RealPlaceContragredientReduction
import Langlands.Global.RankinSelberg.RealStandardDualPairingProof
import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLProof
import Langlands.Global.RankinSelberg.RealStandardPairingReduction
import Langlands.Global.RankinSelberg.RealUniformContinuationReduction
import Langlands.Global.RankinSelberg.UnequalPointwiseFactorizationFromOrdinary

/-! # Unequal pointwise factorization from real continuation and ordinary tests -/

noncomputable section

open NumberField MeasureTheory
open Langlands.LocalFactor.Archimedean
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

/-- Uniform real unequal-rank continuation implies the actual real unequal-rank equation. -/
theorem realUnequalFunctionalEquation_of_uniformContinuation
    (hC : RealLocalUniformUnequalContinuationStatement) :
    RealUnequalFunctionalEquationStatement.{u} := by
  intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' v a ha
    ds es dds ees hds hes hdds hees D W V hW hV
  change RealJacquet.UnequalEquation h a D W V ds es dds ees a
    (realMinusOneScalar T' v ^ r)
  have hWm := (realPlaceUniformWhittakerModel F ψ hψ r T v a ha ds hds W).1 hW
  have hVm := (realPlaceUniformWhittakerModel F ψ hψ t T' v a ha es hes V).2 hV
  have hEq := realLocalUniformUnequalJacquet_of_continuation hC
    r t h ds es hds.1 hes.1 a D W V hWm hVm
  have hDen := realPlaceContragredientPairL
    F r t T Td T' Td' hTd hTd' v ds es dds ees hds hes hdds hees
  have hc := RealLocalJacquet.realMinusOneScalar_eq_parameter T v ds hds
  have hc' := RealLocalJacquet.realMinusOneScalar_eq_parameter T' v es hes
  have hSource : RealJacquet.UnequalEquation h a D W V ds es dds ees (-a)
      (realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v) := by
    simpa only [RealJacquet.UnequalEquation, ← hDen, ← hc, ← hc'] using hEq
  apply RealJacquet.EquationPackage.change_factor hSource
  intro s
  rw [RealJacquet.pair_epsilon_neg,
    realPairCentralCompatibility_of_standardNonzero realStandardKFiniteNonzero
      F r t T T' v ds es hds hes]
  calc
    _ = ((realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v) *
        (realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v ^ (r + 1))) *
        (realPairEpsilon ds es a (NNReal.sqrt ‖(a : ℝ)‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) := by ring
    _ = _ := by
      rw [RealJacquet.unequal_sign _ _
        (realMinusOneScalar_sq T v) (realMinusOneScalar_sq T' v)]

/-- Uniform real unequal-rank continuation and ordinary tests give the exact global
pointwise factorization. The complex ordinary test premise concerns smaller rank at least two. -/
def UnequalPointwiseFactorizationFromRealContinuationStatement : Prop :=
  RealLocalUniformUnequalContinuationStatement →
    RealUnequalOrdinaryPlaceTestsStatement.{u} →
    ComplexUnequalOrdinaryPlaceTestsPositiveRankStatement.{u} →
    UnequalPointwiseFactorizationStatement.{u, uQ}

theorem unequalPointwiseFactorizationFromRealContinuation :
    UnequalPointwiseFactorizationFromRealContinuationStatement.{u, uQ} :=
  fun hC hReal hComplex =>
    unequalPointwiseFactorizationFromOrdinary infiniteWhittakerSliceModel
      (realUnequalPlaceTests_of_ordinary
        (realUnequalFunctionalEquation_of_uniformContinuation hC) hReal)
      hComplex

end Langlands.Global.RankinSelbergGlobal
