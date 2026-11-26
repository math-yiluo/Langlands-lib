import Langlands.Global.AdelicUnipotentConstantTermDifferentiation
import Langlands.Global.AdelicCompactConstantTermCovariance
import Langlands.Automorphic.GroupSchemeEnvelopingAction

/-! # The actual constant-term slice intertwines archimedean differentiation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme InfiniteAdelicGroupPoints AdelicGroupPoints
  Langlands.Geometry.Manifold

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine U.X.left] [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "A" => AdelicGroupPoints F G
local notation "M" => InfiniteAdelicGroupPoints F G
local notation "V" => FinitePlotSmoothRationalFunctions F G
local notation "Γ" => SubgroupFunctor.range j
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G Γ

local instance : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ

include hs hc hu in
private theorem constantTermSlice_smooth_and_differential (f : V) (b : FiniteAdelicGroupPoints F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
      (fun a : M => subgroupConstantTerm F j (evaluate F G f.val) (pair F G a b)) ∧
    ∀ (X : smoothModel F d) (a : M),
      groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
        (fun x : M => subgroupConstantTerm F j (evaluate F G f.val) (pair F G x b)) a =
        subgroupConstantTerm F j (evaluate F G (finitePlotSmoothDifferentialAction F G hsmooth X f).val)
          (pair F G a b) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  obtain ⟨L, hL⟩ := f.property.2
  let φ := evaluate F G f.val
  have hφ : Continuous φ := f.val.property
  have hφS (c : FiniteAdelicGroupPoints F G) : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
      (fun a : M => φ (pair F G a c)) :=
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (finitePlotSmoothSlice F G c f).property
  have hφR (q : RationalGroupPoints F U) (x : A) : φ (map F U G j (rational F U q) * x) = φ x := by
    rw [map_rational]
    exact f.val.val.property _ _
  have hφL (l : FiniteAdelicGroupPoints F G) (hl : l ∈ L.toSubgroup) (x : A) :
      φ (x * ofFinite F G l) = φ x :=
    congrArg (fun y : ContinuousRationalFunctions F G => evaluate F G y x) (hL ⟨l, hl⟩)
  have h := (adelicUnipotentConstantTermDifferentiation j hsmooth hs hc hu
      L.toSubgroup L.isOpen φ hφ hφS hφR hφL).2 b
  refine ⟨h.1, fun X a => ?_⟩
  rw [h.2 X a]
  congr 1
  funext x
  rw [← pair_projections F G x, adelicDirectionalValue_pair,
    evaluate_finitePlotSmoothDifferentialAction]
  rfl

/-- The original normalized constant term, restricted to one finite slice, is an actual
plot-smooth function. This map uses the compact rational quotient of the unipotent subgroup. -/
def plotSmoothConstantTermSlice (b : FiniteAdelicGroupPoints F G) :
    V →ₗ[ℂ] InfinitePlotSmoothFunctions F G := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G Γ : Set A) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hs hc hu
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G Γ
  let measureU := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G Γ
  let : IsProbabilityMeasure measureU :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G Γ
  let T := compactConstantTermLinearMap F G Γ measureU
  let S : V →ₗ[ℂ] (M → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun x => pair F G x b)).comp
      (T.comp (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype)
  have hS (f : V) : S f = fun a => subgroupConstantTerm F j (evaluate F G f.val) (pair F G a b) := by
    funext a
    exact (subgroupConstantTerm_eq_continuousConstantTerm j f.val (pair F G a b)).symm
  refine S.codRestrict _ fun f => ?_
  rw [hS]
  exact (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
    (constantTermSlice_smooth_and_differential j hs hc hu hsmooth f b).1

theorem plotSmoothConstantTermSlice_apply (b : FiniteAdelicGroupPoints F G) (f : V) (x : M) :
    (plotSmoothConstantTermSlice j hs hc hu hsmooth b f).val x =
      subgroupConstantTerm F j (evaluate F G f.val) (pair F G x b) :=
  (subgroupConstantTerm_eq_continuousConstantTerm j f.val (pair F G x b)).symm

/-- The constant-term slice commutes with every real right-orbit derivative. -/
theorem plotSmoothConstantTermSlice_differential (b : FiniteAdelicGroupPoints F G)
    (X : smoothModel F d) (f : V) :
    plotSmoothConstantTermSlice j hs hc hu hsmooth b
        (finitePlotSmoothDifferentialAction F G hsmooth X f) =
      plotSmoothDifferential F G hsmooth X (plotSmoothConstantTermSlice j hs hc hu hsmooth b f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  apply Subtype.ext
  funext a
  rw [plotSmoothConstantTermSlice_apply]
  change _ = groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
    (fun x => (plotSmoothConstantTermSlice j hs hc hu hsmooth b f).val x) a
  simp only [plotSmoothConstantTermSlice_apply]
  exact ((constantTermSlice_smooth_and_differential j hs hc hu hsmooth f b).2 X a).symm

/-- The actual constant-term slice intertwines the full archimedean enveloping action. -/
theorem plotSmoothConstantTermSlice_enveloping (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (b : FiniteAdelicGroupPoints F G) (D : AdelicEnvelopingAlgebra F G hsmooth) (f : V) :
    plotSmoothConstantTermSlice j hs hc hu hsmooth b (adelicEnvelopingAction F G hsmooth hcalc D f) =
      plotSmoothEnvelopingAction F G hsmooth hcalc D (plotSmoothConstantTermSlice j hs hc hu hsmooth b f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) M := LieGroup.of_le (n := ∞) (by simp)
  let S := plotSmoothConstantTermSlice j hs hc hu hsmooth b
  let A₁ := adelicEnvelopingAction F G hsmooth hcalc
  let A₂ := plotSmoothEnvelopingAction F G hsmooth hcalc
  change S (A₁ D f) = A₂ D (S f)
  obtain ⟨z, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) M)) D
  induction z using TensorAlgebra.induction generalizing f with
  | algebraMap a =>
    let Z := AdelicEnvelopingAlgebra F G hsmooth
    change S (A₁ (algebraMap ℂ Z a) f) = A₂ (algebraMap ℂ Z a) (S f)
    rw [show A₁ (algebraMap ℂ Z a) = algebraMap ℂ (Module.End ℂ V) a from A₁.commutes a,
      show A₂ (algebraMap ℂ Z a) = algebraMap ℂ (Module.End ℂ (InfinitePlotSmoothFunctions F G)) a
        from A₂.commutes a]
    exact S.map_smul a f
  | «ι» X =>
    change S (A₁ (UniversalEnvelopingAlgebra.ι ℂ X) f) = A₂ (UniversalEnvelopingAlgebra.ι ℂ X) (S f)
    simp only [A₁, A₂, finitePlotSmoothEnvelopingAction_generator, plotSmoothEnvelopingAction_generator]
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      simp only [complexFinitePlotSmoothLieAction_tmul, complexPlotSmoothLieAction_tmul,
        LinearMap.smul_apply, map_smul]
      exact congrArg (c • ·) (plotSmoothConstantTermSlice_differential j hs hc hu hsmooth b X f)
    | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]
  | mul x y hx hy => simp only [map_mul, Module.End.mul_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end Langlands.Automorphic.GroupSchemeFunctions
