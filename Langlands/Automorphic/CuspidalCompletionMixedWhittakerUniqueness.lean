import Langlands.Automorphic.AdelicHilbertCoordinateActions
import Langlands.Automorphic.CuspidalHilbertIntertwinerCore
import Langlands.Automorphic.CuspidalMixedWhittakerStandardCharacter

/-! # Mixed Whittaker uniqueness on a compatible cuspidal completion -/

noncomputable section
open NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000
set_option Elab.async false

namespace Langlands.Automorphic

open Langlands.Global RankinSelbergGlobal RankinSelbergGlobal.ArchimedeanWhittakerRegularity
open Langlands.Archimedean MixedSmooth OperatorDeterminantSlice CuspidalFixedSmoothDensity
open Langlands.HarmonicAnalysis
universe u

attribute [local instance] regRationalAddCommGroup regContinuousAddCommGroup regSmoothAddCommGroup
  regFormsAddCommGroup regStableAddCommGroup regRealizationAddCommGroup
  finiteAdelicGL_nonarchimedeanGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) {b : T.realization.UnitaryForm}
  (B : OperatorUnitaryFormCore.AdelicCompletion b)

local notation "σ" => finiteHilbertAction F (r + 1) B.action
local notation "π" => infiniteHilbertAction F (r + 1) B.action
local notation "cm" => hilbertCoordinateActions_commute F (r + 1) B.action

/-- Mixed Whittaker uniqueness on the given completion follows from compatible
source maps, density at every finite level and the archimedean slice comparison. -/
def CompletionMixedWhittakerUniqueness : Prop :=
  ∀ (j : T.realization.finiteRepresentation.IntertwiningMap
      (MixedSmooth.finiteRepresentation (A := ArchimedeanMatrix F (r + 1)) σ π cm))
    (s : T.Space →ₗ[ℂ] Langlands.Archimedean.smoothVectors 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) π),
    (∀ v, (j v).val = s v) →
    DenseFixedImages (A := ArchimedeanMatrix F (r + 1)) T.realization.finiteRepresentation σ π s →
    (∀ η : UnitaryAdditiveCharacter (Adeles F), IsStandardAdditiveCharacter F η.complex →
      HasArchimedeanWhittakerSliceComparison T σ π cm j η) →
    ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    MixedWhittakerUniqueness (r := r) ψ σ π cm

set_option maxHeartbeats 12000 in
/-- Apply the mixed tensor comparison to the two restrictions of this action. -/
theorem completionMixedWhittakerUniqueness : CompletionMixedWhittakerUniqueness T B := by
  intro j s hjs hd harch ψ hψ
  exact @mixedWhittakerUniqueness_of_standardCharacter F _ _ _ r T b.HilbertCompletion _ _
    σ π cm j s hjs hd harch ψ hψ

end Langlands.Automorphic
