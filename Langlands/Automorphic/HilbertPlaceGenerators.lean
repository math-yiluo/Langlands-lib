import Langlands.Automorphic.HilbertPlaceClosureCompatibility
import Langlands.Automorphic.CuspidalHilbertRealGenerators

/-! # Actual local Hilbert orbit derivatives from coefficient lifts -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ContDiff Manifold Matrix.Norms.Operator

namespace Langlands.Automorphic.HilbertCoefficientComparison

open Langlands.Global ArchimedeanGL Langlands.Archimedean
universe u uA uG uV uE

private theorem mfderiv_comp_units_val {A : Type uA} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (f : A → ℂ) (g : Aˣ)
    (hf : DifferentiableAt ℝ f (g : A)) :
    mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (f ∘ Units.val) g = fderiv ℝ f (g : A) := by
  have he : (Units.val : Aˣ → A) = extChartAt 𝓘(ℝ, A) g := rfl
  rw [mfderiv_comp g hf.mdifferentiableAt
    ((Units.contMDiff_val (n := ∞)).mdifferentiableAt (by simp)),
    he, mfderiv_extChartAt_self, mfderiv_eq_fderiv]
  rfl

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (U : AdelicGL F n →* (E →L[ℂ] E))

/-- Joint continuity descends to the action at a single place. -/
theorem isContinuousRepresentation_placeAction {G : Type uG} [Group G] [TopologicalSpace G]
    (ι : G →* ArchimedeanGL F n) (hι : Continuous ι) (hU : IsContinuousRepresentation U) :
    IsContinuousRepresentation (placeAction U ι) := by
  have hc : Continuous (fun g : G => AdelicGL.ofInfinite F n
      ((archimedeanGLCoordinates F n).symm (ι g))) :=
    (AdelicGL.ofInfinite F n).continuous.comp ((archimedeanGLCoordinates F n).symm.continuous.comp hι)
  exact hU.comp ((hc.comp continuous_fst).prodMk continuous_snd)

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  (ι : Aˣ →* ArchimedeanGL F n)

/-- Smoothness of an original vector for the mixed real group gives smoothness
of its orbit under an included local group. -/
theorem isSmoothVector_placeAction (hι : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ArchimedeanMatrix F n) ∞ ι)
    {x : E} (hx : Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F n)
      (U.comp (OperatorDeterminantSlice.infiniteCoordinateInclusion F n)) x) :
    Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, A) (placeAction U ι) x :=
  hx.comp hι

/-- The restricted joint-finite lifts identify the local derivative with the
original generator in the inserted real Lie direction. -/
theorem placeAction_realGeneratorCompatibility
    (j : V →ₗ[ℂ] E) (D : EnvelopingAlgebra F n → V → V)
    (hcoeff : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j D)
    (a : A → ArchimedeanMatrix F n) (L : A → RealLieAlgebra F n)
    (ha : ∀ g : Aˣ, a (g : A) = (ι g : ArchimedeanMatrix F n))
    (han : ∀ (f : SmoothFunctions F n) (g : Aˣ),
      AnalyticAt ℝ (coordinateExtension F n f) (ι g : ArchimedeanMatrix F n) →
        AnalyticAt ℝ (coordinateExtension F n f ∘ a) (g : A))
    (hder : ∀ (f : SmoothFunctions F n) (g : Aˣ) (X : A),
      fderiv ℝ (coordinateExtension F n f ∘ a) (g : A) ((g : A) * X) =
        (smoothDifferential F n (L X) f).val ((archimedeanGLCoordinates F n).symm (ι g)))
    (hs : ∀ v, Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, A) (placeAction U ι) (j v)) :
    RealGeneratorCompatibility (placeAction U ι) j
      (fun X v => D (envelopingGenerator F n (complexify F n (L X))) v) id := by
  intro X v
  apply ext_inner_left ℂ
  intro w
  obtain ⟨C, hC, hD, hfin⟩ := hcoeff w
  let t := envelopingGenerator F n (complexify F n (L X))
  let f := coordinateExtension F n (C v) ∘ a
  have hval (g : Aˣ) : f (g : A) = Inner.inner ℂ w (placeAction U ι g (j v)) := by
    change coordinateExtension F n (C v) (a g) = _
    rw [ha, coordinateExtension_apply]
    exact hC v _
  have hfun : (fun g : Aˣ => Inner.inner ℂ w (placeAction U ι g (j v))) = f ∘ Units.val :=
    funext fun g => (hval g).symm
  have hdiff : DifferentiableAt ℝ f ((1 : Aˣ) : A) :=
    (han (C v) 1 (jointFiniteAnalyticity F n (C v) (hfin v) (ι 1))).differentiableAt
  have hcov : C (D t v) = smoothDifferential F n (L X) (C v) := by
    have h := hD t v
    change C (D t v) = envelopingAction F n
      (envelopingGenerator F n (complexify F n (L X))) (C v) at h
    rwa [envelopingAction_real_generator] at h
  have hX := hder (C v) 1 X
  rw [Units.val_one, one_mul, map_one, map_one] at hX
  have hpoint : (C (D t v)).val 1 = Inner.inner ℂ w (j (D t v)) := by
    simpa only [map_one, one_apply_eq_self] using hC (D t v) 1
  change Inner.inner ℂ w (j (D t v)) =
    Inner.inner ℂ w (lieDerivative 𝓘(ℝ, A) (placeAction U ι) X (j v))
  calc
    _ = (C (D t v)).val 1 := hpoint.symm
    _ = (smoothDifferential F n (L X) (C v)).val 1 :=
      congrArg (fun s : SmoothFunctions F n => s.val 1) hcov
    _ = fderiv ℝ f (1 : A) X := hX.symm
    _ = mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ)
        (fun g => Inner.inner ℂ w (placeAction U ι g (j v))) 1 X := by
      rw [hfun, mfderiv_comp_units_val f 1 hdiff, Units.val_one]
      rfl
    _ = _ := (inner_lieDerivative (placeAction U ι) (hs v) w X).symm

end Langlands.Automorphic.HilbertCoefficientComparison
