import Langlands.Global.ArchimedeanEnvelopingAction
import Mathlib.Topology.LocallyConstant.Basic

/-! # Locally constant multiplication and genuine archimedean differentials -/

noncomputable section

universe u

open scoped Classical Manifold ContDiff Matrix.Norms.Operator TensorProduct
open Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- Actual multiplication by a locally constant scalar function preserves real smoothness. -/
theorem locallyConstant_mul_mem
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) (f : SmoothFunctions F n) :
    (fun g => c g * f.val g) ∈ smoothFunctions F n := by
  let : CompleteSpace (ArchimedeanMatrix F n) :=
    inferInstanceAs (CompleteSpace
      (Fin n → Fin n → NumberField.mixedEmbedding.mixedSpace F))
  have hcc := hc.comp_continuous (archimedeanGLCoordinates F n).symm.continuous
  intro x
  have hs := (smoothFunctions F n).smul_mem
    (c ((archimedeanGLCoordinates F n).symm x)) f.property
  refine ContMDiffAt.congr_of_eventuallyEq (hs x) ?_
  filter_upwards [hcc.eventually_eq x] with y hy
  exact congrArg (fun z : ℂ =>
    z * f.val ((archimedeanGLCoordinates F n).symm y)) hy

/-- The complex-linear multiplication operator on the existing smooth functions. -/
def locallyConstantMultiplier
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) : Module.End ℂ (SmoothFunctions F n) where
  toFun f := ⟨fun g => c g * f.val g, locallyConstant_mul_mem F n c hc f⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' z f := by
    apply Subtype.ext
    funext x
    exact mul_left_comm _ _ _

@[simp]
theorem locallyConstantMultiplier_apply
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) (f : SmoothFunctions F n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (locallyConstantMultiplier F n c hc f).val g = c g * f.val g := rfl

/-- Near a unit, the multiplied coordinate extension has a constant scalar factor. -/
theorem coordinateExtension_locallyConstantMultiplier_eventuallyEq
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) (f : SmoothFunctions F n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    coordinateExtension F n (locallyConstantMultiplier F n c hc f) =ᶠ[𝓝
      (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n)]
        c g • coordinateExtension F n f := by
  have ht := (unitsChart F n).tendsto_symm
    (show archimedeanGLCoordinates F n g ∈ (unitsChart F n).source from trivial)
  have hcoords := ((archimedeanGLCoordinates F n).symm.continuous.tendsto
    (archimedeanGLCoordinates F n g)).comp ht
  simp only [unitsChart, IsOpenEmbedding.toOpenPartialHomeomorph_apply] at hcoords
  change Filter.Tendsto
    (fun a : ArchimedeanMatrix F n =>
      (archimedeanGLCoordinates F n).symm ((unitsChart F n).symm a))
    (𝓝 (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n))
    (𝓝 ((archimedeanGLCoordinates F n).symm (archimedeanGLCoordinates F n g)))
    at hcoords
  rw [ContinuousMulEquiv.symm_apply_apply] at hcoords
  have he : ∀ᶠ a in 𝓝
      (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n),
      c ((archimedeanGLCoordinates F n).symm ((unitsChart F n).symm a)) = c g := by
    exact hcoords.eventually (hc.eventually_eq g)
  filter_upwards [he] with a ha
  change c ((archimedeanGLCoordinates F n).symm ((unitsChart F n).symm a)) *
      coordinateExtension F n f a = c g * coordinateExtension F n f a
  rw [ha]

/-- Every actual real directional differential commutes with locally constant multiplication. -/
theorem smoothDifferential_locallyConstantMultiplier
    (X : RealLieAlgebra F n)
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) :
    smoothDifferential F n X * locallyConstantMultiplier F n c hc =
      locallyConstantMultiplier F n c hc * smoothDifferential F n X := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  change fderiv ℝ (coordinateExtension F n (locallyConstantMultiplier F n c hc f))
      (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n) _ =
    c g * (smoothDifferential F n X f).val g
  rw [(coordinateExtension_locallyConstantMultiplier_eventuallyEq F n c hc f g).fderiv_eq,
    fderiv_const_smul
      ((coordinateExtension_contDiffAt F n f _).differentiableAt (by simp))]
  rfl

/-- Complexifying the actual differential preserves commutation with the multiplier. -/
theorem complexSmoothLieAction_locallyConstantMultiplier
    (X : ComplexLieAlgebra F n)
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) :
    complexSmoothLieAction F n X * locallyConstantMultiplier F n c hc =
      locallyConstantMultiplier F n c hc * complexSmoothLieAction F n X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexSmoothLieAction_tmul, smul_mul_assoc, mul_smul_comm]
    exact congrArg (fun T : Module.End ℂ (SmoothFunctions F n) => z • T)
      (smoothDifferential_locallyConstantMultiplier F n X c hc)
  | add X Y hX hY =>
    simp only [map_add, add_mul, mul_add, hX, hY]

/-- Every actual enveloping differential commutes with locally constant multiplication. -/
theorem envelopingAction_locallyConstantMultiplier
    (u : EnvelopingAlgebra F n)
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) :
    envelopingAction F n u * locallyConstantMultiplier F n c hc =
      locallyConstantMultiplier F n c hc * envelopingAction F n u := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ComplexLieAlgebra F n)) u
  change envelopingAction F n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) *
      locallyConstantMultiplier F n c hc =
    locallyConstantMultiplier F n c hc *
      envelopingAction F n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t)
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    simp only [AlgHom.commutes]
    exact Algebra.commutes z (locallyConstantMultiplier F n c hc)
  | ι X =>
    change envelopingAction F n (envelopingGenerator F n X) * _ =
      _ * envelopingAction F n (envelopingGenerator F n X)
    rw [envelopingAction_generator]
    exact complexSmoothLieAction_locallyConstantMultiplier F n X c hc
  | mul x y hx hy =>
    simp only [map_mul]
    calc
      _ = envelopingAction F n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ x) *
          (envelopingAction F n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ y) *
            locallyConstantMultiplier F n c hc) := mul_assoc _ _ _
      _ = _ := by rw [hy, ← mul_assoc, hx, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, add_mul, mul_add, hx, hy]

theorem envelopingAction_locallyConstantMultiplier_apply
    (u : EnvelopingAlgebra F n)
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) (f : SmoothFunctions F n) :
    envelopingAction F n u (locallyConstantMultiplier F n c hc f) =
      locallyConstantMultiplier F n c hc (envelopingAction F n u f) :=
  LinearMap.congr_fun (envelopingAction_locallyConstantMultiplier F n u c hc) f

theorem envelopingAction_locallyConstantMultiplier_eval
    (u : EnvelopingAlgebra F n)
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) (f : SmoothFunctions F n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (envelopingAction F n u (locallyConstantMultiplier F n c hc f)).val g =
      c g * (envelopingAction F n u f).val g := by
  rw [envelopingAction_locallyConstantMultiplier_apply, locallyConstantMultiplier_apply]

theorem centerAction_locallyConstantMultiplier
    (z : EnvelopingCenter F n)
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) → ℂ)
    (hc : IsLocallyConstant c) (f : SmoothFunctions F n) :
    centerAction F n z (locallyConstantMultiplier F n c hc f) =
      locallyConstantMultiplier F n c hc (centerAction F n z f) :=
  envelopingAction_locallyConstantMultiplier_apply F n (centerInclusion F n z) c hc f

end Langlands.Global.ArchimedeanGL
