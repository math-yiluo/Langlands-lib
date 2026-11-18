import Langlands.Automorphic.CuspidalHilbertCoefficientValues
import Langlands.Automorphic.CuspidalHilbertScalarGeneratorLifts

/-! # Genuine real generators of the conditional actual Hilbert action -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical Manifold ContDiff

namespace Langlands.Archimedean
universe pA pG pV pE pX
variable {A : Type pA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type pG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {V : Type pV} [AddCommGroup V] [Module ℂ V]
  {E : Type pE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {X : Type pX}

/-- An injective prescribed linear map has genuine smooth values and preserves
all its prescribed real generators under the actual orbit derivative. -/
def SmoothGeneratorComparison (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E)
    (D : X → V → V) (ζ : X → A) : Prop :=
  (∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v)) ∧ Function.Injective j ∧
    RealGeneratorCompatibility π j D ζ

theorem smoothGeneratorComparison_of_compatibility
    (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E) (D : X → V → V) (ζ : X → A)
    (hs : ∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v)) (hj : Function.Injective j)
    (hD : RealGeneratorCompatibility π j D ζ) :
    SmoothGeneratorComparison π j D ζ := ⟨hs, hj, hD⟩

end Langlands.Archimedean

namespace Langlands.Automorphic
open Langlands.Global MeasureTheory
open scoped NumberField Matrix.Norms.Operator
universe u
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance hilbertFinalGeneratorRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertFinalGeneratorContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertFinalGeneratorFiniteGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertFinalGeneratorFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance hilbertFinalGeneratorStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertFinalGeneratorSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)
  (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ∀ f g : T.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F (r + 1) T.realization f q)
      (toQuotient F (r + 1) T.realization g q)
      ∂(quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))

/-- The original real enveloping generators are the genuine Hilbert orbit
derivatives on every source vector, under the two named analytic premises. -/
theorem realGeneratorCompatibility
    (hkernel : Langlands.Archimedean.HilbertSmoothKernelStatement.{u, u, u}) :
    Langlands.Archimedean.RealGeneratorCompatibility
      (coordinateHilbertRepresentation T hcoeff χ hχ hTχ b hb) b.finiteForm.toHilbert
      (fun X v => T.realization.envelopingAction (ArchimedeanGL.envelopingGenerator F (r + 1)
        (ArchimedeanGL.complexify F (r + 1) X)) v)
      (ArchimedeanGL.realLieAlgebraToMatrix F (r + 1)) :=
  Langlands.Archimedean.realGeneratorCompatibility_of_scalar
    (coordinateHilbertRepresentation T hcoeff χ hχ hTχ b hb) b.finiteForm.toHilbert
    (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r) χ hχ hTχ b hb 1)
    (fun w v g => CuspidalHilbertOrbitCoefficient.coefficient T w v
      ((archimedeanGLCoordinates F (r + 1)).symm g))
    (fun X v => T.realization.envelopingAction (ArchimedeanGL.envelopingGenerator F (r + 1)
      (ArchimedeanGL.complexify F (r + 1) X)) v)
    (ArchimedeanGL.realLieAlgebraToMatrix F (r + 1))
    (scalarCoefficientValues T hcoeff χ hχ hTχ b hb)
    (toHilbert_isSmoothVector T hcoeff χ hχ hTχ b hb hkernel)
    (scalarGeneratorLifts_of_coefficients T hcoeff ⟨χ, hχ, hTχ⟩)

end OperatorDeterminantSlice

/-- Genuine smooth source vectors and exact real generators on the original
form completion, retaining both named analytic premises. -/
def CuspidalHilbertSmoothEmbeddingStatement : Prop :=
  ∀ (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
    (_hkernel : Langlands.Archimedean.HilbertSmoothKernelStatement.{u, u, u})
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
    (b : T.realization.UnitaryForm)
    (hb : ∀ f g : T.Space, b.inner f g =
      ∫ q, Inner.inner ℂ (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization f q)
        (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization g q)
        ∂(OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
          (OperatorDeterminantSlice.band F (r + 1))),
    Langlands.Archimedean.SmoothGeneratorComparison
      (OperatorDeterminantSlice.coordinateHilbertRepresentation T hcoeff χ hχ hTχ b hb)
      b.finiteForm.toHilbert
      (fun X v => T.realization.envelopingAction (ArchimedeanGL.envelopingGenerator F (r + 1)
        (ArchimedeanGL.complexify F (r + 1) X)) v)
      (ArchimedeanGL.realLieAlgebraToMatrix F (r + 1))

theorem cuspidalHilbertSmoothEmbedding : CuspidalHilbertSmoothEmbeddingStatement.{u} := by
  intro hcoeff hkernel F _ _ _ r T χ hχ hTχ b hb
  exact Langlands.Archimedean.smoothGeneratorComparison_of_compatibility
    (OperatorDeterminantSlice.coordinateHilbertRepresentation T hcoeff χ hχ hTχ b hb)
    b.finiteForm.toHilbert
    (fun X v => T.realization.envelopingAction (ArchimedeanGL.envelopingGenerator F (r + 1)
      (ArchimedeanGL.complexify F (r + 1) X)) v)
    (ArchimedeanGL.realLieAlgebraToMatrix F (r + 1))
    (OperatorDeterminantSlice.toHilbert_isSmoothVector T hcoeff χ hχ hTχ b hb hkernel)
    b.finiteForm.toHilbert_injective
    (OperatorDeterminantSlice.realGeneratorCompatibility T hcoeff χ hχ hTχ b hb hkernel)

end Langlands.Automorphic
