import Langlands.Global.InfiniteAdelicRestrictionSmooth
import Langlands.Algebra.EnvelopingCharacterShift
import Langlands.Automorphic.GroupSchemeEnvelopingAction
import Langlands.Automorphic.GroupSchemeForms
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Multiplication by a smooth character and the enveloping action on `G(F_∞)`

For a smooth function `χ` on a Lie group with `χ(xy) = χ(x)χ(y)`, the Leibniz rule gives
`D_X(χ u) = χ (D_X u + dχ(X) u)` for the right orbit derivatives `D_X`, where `dχ(X)` is the
derivative of `χ` at the identity. On the infinite adelic points of a group scheme, with the
Library's complexified enveloping action, this makes multiplication by `χ` intertwine the action
of every element `y` with the action of `shift dχ y`, where `shift dχ` is the automorphism of
the enveloping algebra extending `U ↦ U + dχ(U)`. In particular there is one algebra
endomorphism `θ` of the center of the enveloping algebra with `z (χ u) = χ (θ(z) u)` for all
`z` and all plot-smooth `u`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- The Leibniz rule for the right orbit derivative of a product of smooth functions. -/
theorem groupDirectionalValue_fun_mul (X : GroupLieAlgebra I G) {f h : G → ℂ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℂ) ∞ h) (g : G) :
    groupDirectionalValue I X (fun x => f x * h x) g =
      groupDirectionalValue I X f g * h g + f g * groupDirectionalValue I X h g := by
  let p (z : G) := f (g * z)
  let q (z : G) := h (g * z)
  have hm : ContMDiff I I ∞ (fun z : G => g * z) := contMDiff_const.mul contMDiff_id
  have hp : MDifferentiableAt I 𝓘(ℝ, ℂ) p (1 : G) := (hf.comp hm).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt I 𝓘(ℝ, ℂ) q (1 : G) := (hh.comp hm).mdifferentiableAt (by simp)
  have hd := hp.hasMFDerivAt.mul hq.hasMFDerivAt
  have hd' : mvfderiv I (p * q) 1 = p 1 • mvfderiv I q 1 + q 1 • mvfderiv I p 1 := hd.mfderiv
  have hX := congrArg (fun D : TangentSpace I (1 : G) →L[ℝ] ℂ => D X) hd'
  have hp1 : p 1 = f g := by simp only [p, mul_one]
  have hq1 : q 1 = h g := by simp only [q, mul_one]
  change mvfderiv I (p * q) 1 X = mvfderiv I p 1 X * h g + f g * mvfderiv I q 1 X
  simp only [add_apply, smul_apply, smul_eq_mul,
    hp1, hq1] at hX
  rw [hX]
  ring

/-- The right orbit derivative of a smooth multiplicative function is the function times its
derivative at the identity. -/
theorem groupDirectionalValue_of_map_mul (X : GroupLieAlgebra I G) {χ : G → ℂ}
    (hχ : ContMDiff I 𝓘(ℝ, ℂ) ∞ χ) (hmul : ∀ x y : G, χ (x * y) = χ x * χ y) (g : G) :
    groupDirectionalValue I X χ g = χ g * groupDirectionalValue I X χ 1 := by
  have h1 : (fun y => χ (g * y)) = (fun y => (χ g • χ) (1 * y)) := by
    funext y
    simp only [hmul, one_mul, Pi.smul_apply, smul_eq_mul]
  change mvfderiv I (fun y => χ (g * y)) 1 X = _
  rw [h1]
  exact groupDirectionalValue_const_smul I X (χ g) hχ 1

end Langlands.Geometry.Manifold

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Geometry.Manifold Langlands.Automorphic.GroupSchemeFunctions

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- Multiplication by a fixed plot-smooth function, as a linear endomorphism of the plot-smooth
functions on `G(F_∞)`. -/
def plotSmoothMultiplication (χ : InfiniteAdelicGroupPoints F G → ℂ)
    (hχ : χ ∈ InfinitePlotSmoothFunctions F G) :
    Module.End ℂ (InfinitePlotSmoothFunctions F G) where
  toFun f := ⟨fun x => χ x * f.val x, mul_mem_infinitePlotSmoothFunctions hχ f.property⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    change χ x * (f.val x + h.val x) = χ x * f.val x + χ x * h.val x
    ring
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change χ x * (c * f.val x) = c * (χ x * f.val x)
    ring

omit [IsAffine G.X.left] in
@[simp]
theorem plotSmoothMultiplication_apply (χ : InfiniteAdelicGroupPoints F G → ℂ)
    (hχ : χ ∈ InfinitePlotSmoothFunctions F G) (f : InfinitePlotSmoothFunctions F G)
    (x : InfiniteAdelicGroupPoints F G) :
    (plotSmoothMultiplication F G χ hχ f).val x = χ x * f.val x :=
  rfl

/-- Multiplication by a smooth character intertwines the center of the enveloping algebra
with itself: for a plot-smooth `χ` on `G(F_∞)` with `χ(xy) = χ(x)χ(y)` and `χ(1) = 1`, there
is an algebra endomorphism `θ` of the center with `z (χ u) = χ (θ(z) u)` for every central
`z` and every plot-smooth `u`. -/
theorem exists_centerShift_plotSmoothMultiplication
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (χ : InfiniteAdelicGroupPoints F G → ℂ) (hχ : χ ∈ InfinitePlotSmoothFunctions F G)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y) (hone : χ 1 = 1) :
    ∃ θ : AdelicEnvelopingCenter F G hsmooth →ₐ[ℂ] AdelicEnvelopingCenter F G hsmooth,
      ∀ (z : AdelicEnvelopingCenter F G hsmooth) (f : InfinitePlotSmoothFunctions F G),
        plotSmoothCenterAction F G hsmooth hcalc z (plotSmoothMultiplication F G χ hχ f) =
          plotSmoothMultiplication F G χ hχ (plotSmoothCenterAction F G hsmooth hcalc (θ z) f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let I := 𝓘(ℝ, smoothModel F d)
  let L := GroupLieAlgebra I (InfiniteAdelicGroupPoints F G)
  let ρℝ := realPlotSmoothLieAction F G hsmooth hcalc
  let ρ := Algebra.ComplexLieExtension.lie ρℝ
  let T := plotSmoothMultiplication F G χ hχ
  have hχs : ContMDiff I 𝓘(ℝ, ℂ) ∞ χ := (isPlotSmooth_iff_contMDiff F G hsmooth χ).mp hχ
  let c0 : L →ₗ[ℝ] ℂ :=
    { toFun := fun X => groupDirectionalValue I X χ 1
      map_add' := fun X Y => groupDirectionalValue_add_direction I X Y χ 1
      map_smul' := fun r X => groupDirectionalValue_smul_direction I r X χ 1 }
  let mu : ℂ ⊗[ℝ] L →ₗ[ℂ] ℂ := Algebra.ComplexLieExtension.linear c0
  have hT : ∀ Z : ℂ ⊗[ℝ] L,
      ρ Z * T = T * (ρ Z + algebraMap ℂ (Module.End ℂ (InfinitePlotSmoothFunctions F G)) (mu Z)) := by
    intro Z
    induction Z using TensorProduct.inductionOn with
    | tmul w X =>
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext g
      have hfs : ContMDiff I 𝓘(ℝ, ℂ) ∞ f.val :=
        (isPlotSmooth_iff_contMDiff F G hsmooth f.val).mp f.property
      change w * groupDirectionalValue I X (fun x => χ x * f.val x) g =
        χ g * (w * groupDirectionalValue I X f.val g + (w * groupDirectionalValue I X χ 1) * f.val g)
      rw [groupDirectionalValue_fun_mul I X hχs hfs g, groupDirectionalValue_of_map_mul I X hχs hmul g]
      ring
    | add Z W hZ hW =>
      rw [map_add, map_add, map_add, add_mul, hZ, hW, ← mul_add]
      congr 1
      abel
  have hT0 : T ≠ 0 := by
    intro h0
    have h1 := congrArg (fun S : Module.End ℂ (InfinitePlotSmoothFunctions F G) =>
      (S ⟨fun _ => (1 : ℂ), GroupScheme.isPlotSmooth_const G _ _ 1⟩).val 1) h0
    change χ 1 * 1 = 0 at h1
    rw [hone, one_mul] at h1
    exact one_ne_zero h1
  obtain ⟨θ, hθ⟩ :=
    Algebra.EnvelopingCharacterShift.exists_centerShift_intertwining ρ T hT0 mu hT
  refine ⟨θ, fun z f => ?_⟩
  exact LinearMap.congr_fun (hθ z) f

end Langlands.Global.InfiniteAdelicGroupPoints
