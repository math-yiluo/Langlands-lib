import Langlands.Automorphic.GroupSchemeFiniteLevelSlices
import Langlands.Automorphic.GroupSchemeDifferential

/-! # Actual tangent differentiation of finite-smooth adelic functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- Actual slice differentiation retains rational covariance and the specified finite level. -/
def differentiatePlotSliceFamily (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G)) (X : smoothModel F d) :
    Module.End ℂ (FiniteLevelPlotSmoothSliceFamilies F G L) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  refine
    { toFun := fun s => ⟨fun b => plotSmoothDifferential F G hsmooth X (s.val b), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · constructor
    · intro b l
      dsimp only
      rw [s.property.1 b l]
    · intro γ b a
      have hcov :
          plotSmoothLeftTranslation F G
            (AdelicGroupPoints.infinite F G (AdelicGroupPoints.rational F G γ))
            (s.val (AdelicGroupPoints.finite F G (AdelicGroupPoints.rational F G γ) * b)) =
              s.val b := by
        apply Subtype.ext
        funext x
        exact s.property.2 γ b x
      change (plotSmoothLeftTranslation F G
        (AdelicGroupPoints.infinite F G (AdelicGroupPoints.rational F G γ))
        (plotSmoothDifferential F G hsmooth X
          (s.val (AdelicGroupPoints.finite F G (AdelicGroupPoints.rational F G γ) * b)))).val a =
            (plotSmoothDifferential F G hsmooth X (s.val b)).val a
      rw [← plotSmoothDifferential_leftTranslation, hcov]
  · intro s t
    apply Subtype.ext
    funext b
    exact map_add (plotSmoothDifferential F G hsmooth X) (s.val b) (t.val b)
  · intro c s
    apply Subtype.ext
    funext b
    exact map_smul (plotSmoothDifferential F G hsmooth X) c (s.val b)

/-- A finite stabilizer is chosen only to prove joint continuity of the actual derivative. -/
def finitePlotSmoothDifferential (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (X : smoothModel F d) (f : FinitePlotSmoothRationalFunctions F G) :
    FinitePlotSmoothRationalFunctions F G :=
  let L := Classical.choose f.property.2
  let hL := Classical.choose_spec f.property.2
  reconstructFinitePlotSmoothSlices F G hsmooth L
    (differentiatePlotSliceFamily F G hsmooth L X (plotSlicesAtLevel F G L f hL))

@[simp]
theorem finitePlotSmoothSlice_differential
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (X : smoothModel F d)
    (f : FinitePlotSmoothRationalFunctions F G) (b : FiniteAdelicGroupPoints F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    finitePlotSmoothSlice F G b (finitePlotSmoothDifferential F G hsmooth X f) =
      plotSmoothDifferential F G hsmooth X (finitePlotSmoothSlice F G b f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  unfold finitePlotSmoothDifferential
  rw [finitePlotSmoothSlice_reconstruct]
  rfl

/-- Every stabilizer fixing the function gives the same reconstructed derivative. -/
theorem finitePlotSmoothDifferential_eq_reconstruct
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (X : smoothModel F d)
    (L : OpenSubgroup (FiniteAdelicGroupPoints F G))
    (f : FinitePlotSmoothRationalFunctions F G)
    (hf : f.val ∈ levelSubmodule F G L.toSubgroup) :
    finitePlotSmoothDifferential F G hsmooth X f =
      reconstructFinitePlotSmoothSlices F G hsmooth L
        (differentiatePlotSliceFamily F G hsmooth L X (plotSlicesAtLevel F G L f hf)) := by
  apply finitePlotSmoothSlice_injective F G
  funext b
  dsimp only
  rw [finitePlotSmoothSlice_differential, finitePlotSmoothSlice_reconstruct]
  rfl

/-- The actual derivative is complex linear on the unchanged finite-smooth adelic carrier. -/
def finitePlotSmoothDifferentialAction (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (X : smoothModel F d) : Module.End ℂ (FinitePlotSmoothRationalFunctions F G) where
  toFun := finitePlotSmoothDifferential F G hsmooth X
  map_add' f g := by
    apply finitePlotSmoothSlice_injective F G
    funext b
    dsimp only
    simp only [finitePlotSmoothSlice_differential, map_add]
  map_smul' c f := by
    apply finitePlotSmoothSlice_injective F G
    funext b
    dsimp only
    simp only [finitePlotSmoothSlice_differential, map_smul, RingHom.id_apply]

@[simp]
theorem finitePlotSmoothSlice_differentialAction
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (X : smoothModel F d)
    (f : FinitePlotSmoothRationalFunctions F G) (b : FiniteAdelicGroupPoints F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    finitePlotSmoothSlice F G b (finitePlotSmoothDifferentialAction F G hsmooth X f) =
      plotSmoothDifferential F G hsmooth X (finitePlotSmoothSlice F G b f) :=
  finitePlotSmoothSlice_differential F G hsmooth X f b

/-- Evaluation is exactly real differentiation of the original positive right orbit. -/
theorem evaluate_finitePlotSmoothDifferentialAction
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (X : smoothModel F d)
    (f : FinitePlotSmoothRationalFunctions F G)
    (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    evaluate F G (finitePlotSmoothDifferentialAction F G hsmooth X f).val
      (AdelicGroupPoints.pair F G a b) =
        mvfderiv 𝓘(ℝ, smoothModel F d)
          (fun h => evaluate F G f.val (AdelicGroupPoints.pair F G (a * h) b)) 1 X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  exact congrArg (fun s : InfinitePlotSmoothFunctions F G => s.val a)
    (finitePlotSmoothSlice_differentialAction F G hsmooth X f b)

/-- Real linearity in the actual identity tangent survives adelic reconstruction. -/
def realFinitePlotSmoothDifferential (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →ₗ[ℝ]
      Module.End ℂ (FinitePlotSmoothRationalFunctions F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  refine
    { toFun := finitePlotSmoothDifferentialAction F G hsmooth
      map_add' := ?_
      map_smul' := ?_ }
  · intro X Y
    apply LinearMap.ext
    intro f
    apply finitePlotSmoothSlice_injective F G
    funext b
    change finitePlotSmoothSlice F G b
        (finitePlotSmoothDifferentialAction F G hsmooth (X + Y) f) =
      finitePlotSmoothSlice F G b
        (finitePlotSmoothDifferentialAction F G hsmooth X f +
          finitePlotSmoothDifferentialAction F G hsmooth Y f)
    simp only [map_add, finitePlotSmoothSlice_differentialAction]
    exact congrArg (fun D => D (finitePlotSmoothSlice F G b f))
      ((realPlotSmoothDifferential F G hsmooth).map_add X Y)
  · intro c X
    apply LinearMap.ext
    intro f
    apply finitePlotSmoothSlice_injective F G
    funext b
    change finitePlotSmoothSlice F G b
        (finitePlotSmoothDifferentialAction F G hsmooth (c • X) f) =
      finitePlotSmoothSlice F G b (c • finitePlotSmoothDifferentialAction F G hsmooth X f)
    rw [LinearMap.map_smul_of_tower, finitePlotSmoothSlice_differentialAction,
      finitePlotSmoothSlice_differentialAction]
    exact congrArg (fun D => D (finitePlotSmoothSlice F G b f))
      ((realPlotSmoothDifferential F G hsmooth).map_smul c X)

@[simp]
theorem finitePlotSmoothSlice_finiteRightAction
    (b c : FiniteAdelicGroupPoints F G) (f : FinitePlotSmoothRationalFunctions F G) :
    finitePlotSmoothSlice F G b
        (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c) f) =
      finitePlotSmoothSlice F G (b * c) f := by
  apply Subtype.ext
  funext a
  change evaluate F G f.val
    (AdelicGroupPoints.pair F G a b * AdelicGroupPoints.ofFinite F G c) = _
  rw [AdelicGroupPoints.ofFinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one]
  rfl

/-- Actual finite right translation commutes with archimedean tangent differentiation. -/
theorem finitePlotSmoothDifferentialAction_finiteRightAction
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (X : smoothModel F d)
    (c : FiniteAdelicGroupPoints F G) (f : FinitePlotSmoothRationalFunctions F G) :
    finitePlotSmoothDifferentialAction F G hsmooth X
        (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c) f) =
      finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c)
        (finitePlotSmoothDifferentialAction F G hsmooth X f) := by
  apply finitePlotSmoothSlice_injective F G
  funext b
  dsimp only
  rw [finitePlotSmoothSlice_differentialAction, finitePlotSmoothSlice_finiteRightAction,
    finitePlotSmoothSlice_finiteRightAction, finitePlotSmoothSlice_differentialAction]

/-- Every specified finite subgroup fixing the input also fixes its derivative. -/
theorem finitePlotSmoothDifferentialAction_preserves_level
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (X : smoothModel F d)
    (L : Subgroup (FiniteAdelicGroupPoints F G))
    (f : FinitePlotSmoothRationalFunctions F G)
    (hf : f.val ∈ levelSubmodule F G L) :
    (finitePlotSmoothDifferentialAction F G hsmooth X f).val ∈ levelSubmodule F G L := by
  intro l
  have hfix : finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G l.val) f = f :=
    Subtype.ext (hf l)
  have h := congrArg (fun s : FinitePlotSmoothRationalFunctions F G => s.val)
    (finitePlotSmoothDifferentialAction_finiteRightAction F G hsmooth X l.val f)
  rw [hfix] at h
  exact h.symm

/-- Compact finite level, if present, is preserved with the same subgroup. -/
theorem finitePlotSmoothDifferentialAction_hasFiniteLevel
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (X : smoothModel F d)
    (f : FinitePlotSmoothRationalFunctions F G) (hf : HasFiniteLevel F G f.val) :
    HasFiniteLevel F G (finitePlotSmoothDifferentialAction F G hsmooth X f).val := by
  obtain ⟨L, ho, hc, hL⟩ := hf
  exact ⟨L, ho, hc, finitePlotSmoothDifferentialAction_preserves_level F G hsmooth X L f hL⟩

/-- Connected reductivity supplies the canonical actual finite-smooth tangent action. -/
def reductiveRealFinitePlotSmoothDifferential (hG : GroupScheme.IsConnectedReductive G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    GroupLieAlgebra 𝓘(ℝ, smoothModel F hG.smoothDimension)
      (InfiniteAdelicGroupPoints F G) →ₗ[ℝ]
        Module.End ℂ (FinitePlotSmoothRationalFunctions F G) :=
  realFinitePlotSmoothDifferential F G hG.smoothDimension_spec

end Langlands.Automorphic.GroupSchemeFunctions
