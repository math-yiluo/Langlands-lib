import Langlands.Automorphic.GroupSchemeFiniteDifferential
import Langlands.Global.GeneralLinearInfiniteAdelicDifferential
import Langlands.Automorphic.EnvelopingAction

/-! # Original general-linear finite-smooth differential comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance finiteDifferentialGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

variable {d : ℕ}

/-- The unchanged finite-smooth comparison identifies the original smooth slices. -/
@[simp]
theorem finiteSmoothSlice_finitePlotSmoothGeneralLinearEquiv
    (f : FinitePlotSmoothRationalFunctions F GLG) (b : FiniteAdelicGroupPoints F GLG) :
    Langlands.Automorphic.finiteSmoothSlice F n (GeneralLinearGroupPoints.finiteHomeomorph F n b)
        (finitePlotSmoothGeneralLinearEquiv F n f) =
      GeneralLinearGroupPoints.plotSmoothGeneralLinearEquiv F n
        (finitePlotSmoothSlice F GLG b f) := by
  apply Subtype.ext
  exact infiniteSlice_continuousGeneralLinearEquiv F n f.val b

/-- The actual adelic tangent derivative becomes the original finite-smooth
enveloping action on the corresponding real generator. -/
theorem finitePlotSmoothGeneralLinearEquiv_differential
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (X : smoothModel F d) (f : FinitePlotSmoothRationalFunctions F GLG) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F GLG hsmooth
    finitePlotSmoothGeneralLinearEquiv F n
        (finitePlotSmoothDifferentialAction F GLG hsmooth X f) =
      Langlands.Automorphic.finiteSmoothEnvelopingAction F n
        (ArchimedeanGL.envelopingGenerator F n
          (ArchimedeanGL.complexify F n
            (GeneralLinearGroupPoints.infiniteRealLieAlgebraEquiv F n hsmooth X)))
        (finitePlotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  apply Langlands.Automorphic.finiteSmoothSlice_injective F n
  funext b
  obtain ⟨b, rfl⟩ := (GeneralLinearGroupPoints.finiteHomeomorph F n).surjective b
  dsimp only
  rw [finiteSmoothSlice_finitePlotSmoothGeneralLinearEquiv,
    finitePlotSmoothSlice_differentialAction,
    GeneralLinearGroupPoints.plotSmoothGeneralLinearEquiv_differential,
    Langlands.Automorphic.finiteSmoothSlice_envelopingAction,
    ArchimedeanGL.envelopingAction_real_generator,
    finiteSmoothSlice_finitePlotSmoothGeneralLinearEquiv]

/-- Conjugate the actual real tangent action by the original finite-smooth
equivalence, retaining the original matrix function carrier. -/
def generalLinearRealFiniteSmoothDifferential
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F GLG hsmooth
    GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG) →ₗ[ℝ]
      Module.End ℂ (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  exact ((finitePlotSmoothGeneralLinearEquiv F n).conj.toLinearMap.restrictScalars ℝ).comp
    (realFinitePlotSmoothDifferential F GLG hsmooth)

@[simp]
theorem generalLinearRealFiniteSmoothDifferential_apply
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (X : smoothModel F d) (f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F GLG hsmooth
    generalLinearRealFiniteSmoothDifferential F n hsmooth X f =
      finitePlotSmoothGeneralLinearEquiv F n
        (finitePlotSmoothDifferentialAction F GLG hsmooth X
          ((finitePlotSmoothGeneralLinearEquiv F n).symm f)) := rfl

/-- On the original finite-smooth space the conjugated operator is exactly the
existing enveloping generator, with no supplied tangent identification. -/
theorem generalLinearRealFiniteSmoothDifferential_eq_generator
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) (X : smoothModel F d) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F GLG hsmooth
    generalLinearRealFiniteSmoothDifferential F n hsmooth X =
      Langlands.Automorphic.finiteSmoothEnvelopingAction F n
        (ArchimedeanGL.envelopingGenerator F n
          (ArchimedeanGL.complexify F n
            (GeneralLinearGroupPoints.infiniteRealLieAlgebraEquiv F n hsmooth X))) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  apply LinearMap.ext
  intro f
  rw [generalLinearRealFiniteSmoothDifferential_apply,
    finitePlotSmoothGeneralLinearEquiv_differential, LinearEquiv.apply_symm_apply]

/-- The canonical reductive atlas has the same original finite-smooth generator
comparison, for every natural rank. -/
theorem finitePlotSmoothGeneralLinearEquiv_reductiveDifferential
    (X : smoothModel F
      (GroupScheme.isConnectedReductive_generalLinear F (Fin n)).smoothDimension)
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := reductiveChartedSpace F GLG
      (GroupScheme.isConnectedReductive_generalLinear F (Fin n))
    finitePlotSmoothGeneralLinearEquiv F n
        (reductiveRealFinitePlotSmoothDifferential F GLG
          (GroupScheme.isConnectedReductive_generalLinear F (Fin n)) X f) =
      Langlands.Automorphic.finiteSmoothEnvelopingAction F n
        (ArchimedeanGL.envelopingGenerator F n
          (ArchimedeanGL.complexify F n
            (GeneralLinearGroupPoints.reductiveInfiniteRealLieAlgebraEquiv F n X)))
        (finitePlotSmoothGeneralLinearEquiv F n f) :=
  finitePlotSmoothGeneralLinearEquiv_differential F n
    (GroupScheme.isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec X f

end Langlands.Automorphic.GroupSchemeFunctions
