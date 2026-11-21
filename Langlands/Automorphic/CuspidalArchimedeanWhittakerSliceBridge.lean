import Langlands.Automorphic.AdelicHilbertCoordinateActions
import Langlands.Automorphic.CuspidalMixedSliceTensorBridge
import Langlands.Automorphic.CuspidalMixedArchimedeanSliceComparison

/-! # From Hilbert slice comparison to the mixed tensor comparison -/

noncomputable section
open NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Global RankinSelbergGlobal RankinSelbergGlobal.ArchimedeanWhittakerRegularity
open Langlands.Archimedean MixedSmooth CuspidalFixedSmoothDensity OperatorDeterminantSlice
open Langlands.HarmonicAnalysis InfinitePlaceFamily
universe u
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup

section Completion

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) {b : T.realization.UnitaryForm}
  (B : OperatorUnitaryFormCore.AdelicCompletion b)

/-- The archimedean tensor condition for every standard character and compatible
mixed source map on the supplied adelic completion. -/
def CompletionArchimedeanWhittakerSlices : Prop :=
  let σ := finiteHilbertAction F (r + 1) B.action
  let π := infiniteHilbertAction F (r + 1) B.action
  let cm := hilbertCoordinateActions_commute F (r + 1) B.action
  ∀ (ψ : UnitaryAdditiveCharacter (Adeles F)), IsStandardAdditiveCharacter F ψ.complex →
    ∀ (j : T.realization.finiteRepresentation.IntertwiningMap
      (MixedSmooth.finiteRepresentation (A := ArchimedeanMatrix F (r + 1)) σ π cm)),
      (∀ w, (j w).val.val = b.toHilbert w) →
      HasArchimedeanWhittakerSliceComparison T σ π cm j ψ

/-- The local Hilbert comparison supplies the archimedean slot condition
on the same completion. -/
theorem completionArchimedeanWhittakerSlices_of_comparisons
    (h : ∀ (i : Index F) (a : T.finiteInfiniteDecomposition.finite.toSubmodule)
      (x : ∀ j, T.placeDensityModels.subspace j),
        B.HasIndexedWhittakerSliceComparison (T.placeTensorSlice i a x)) :
    CompletionArchimedeanWhittakerSlices T B := by
  intro ψ hψ j hj
  let σ := finiteHilbertAction F (r + 1) B.action
  let π := infiniteHilbertAction F (r + 1) B.action
  let cm := hilbertCoordinateActions_commute F (r + 1) B.action
  exact hasArchimedeanWhittakerSliceComparison_of_algebraicSlices T σ π cm j ψ
    (fun i a x => h i a x ψ.complex hψ j.toLinearMap hj)

end Completion

/-- The actual band completion has the archimedean tensor slice condition,
given local unitary Whittaker uniqueness and the original mixed inclusion. -/
def CuspidalBandArchimedeanWhittakerSliceBridgeStatement : Prop :=
  UnitaryWhittakerMultiplicityOneStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (hTχ : T.realization.HasCentralCharacter χ) (b : T.realization.UnitaryForm)
    (hb : ComputesBandInnerProduct T.realization b),
    CompletionArchimedeanWhittakerSlices T (adelicCompletion T χ hχ hTχ b hb)

theorem cuspidalBandArchimedeanWhittakerSliceBridge :
    CuspidalBandArchimedeanWhittakerSliceBridgeStatement.{u} := by
  intro hUnique F _ _ _ r T χ hχ hTχ b hb
  exact completionArchimedeanWhittakerSlices_of_comparisons T _
    (CuspidalOperatorRealization.cuspidalMixedArchimedeanSliceComparison hUnique F r T χ hχ hTχ b hb)

end Langlands.Automorphic
