import Langlands.Automorphic.TwoBlockConstantTermCovariance
import Langlands.Global.ArchimedeanBlockLieInclusions
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Smooth pullbacks to each diagonal block -/

noncomputable section
universe u

open scoped Classical ContDiff Manifold Matrix.Norms.Operator Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "M" => ArchimedeanMatrix F
local notation "G" => ArchimedeanGL F
local notation "G∞" => InfiniteAdelicGL F
local notation "κ" => archimedeanGLCoordinates F

omit [NumberField F] in
private theorem blockDiagonalEmbedding_coordinates (p : G∞ a × G∞ b) :
    (κ n (blockDiagonalEmbedding h p)).val =
      blockDiagonalMatrixMap F h ((κ a p.1).val, (κ b p.2).val) := by
  change (Matrix.GeneralLinearGroup.map (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
    (blockDiagonalEmbedding h p)).val = _
  rw [map_blockDiagonalEmbedding, blockDiagonalMatrixMap_apply]
  rfl

private def firstBlockMatrixLinear : M a →L[ℝ] M n :=
  ((blockDiagonalMatrixMap F h).comp (LinearMap.inl ℝ (M a) (M b))).toContinuousLinearMap

private def secondBlockMatrixLinear : M b →L[ℝ] M n :=
  ((blockDiagonalMatrixMap F h).comp (LinearMap.inr ℝ (M a) (M b))).toContinuousLinearMap

private theorem firstBlockCoordinates (x : G a) (y : G∞ b) :
    (κ n (blockDiagonalEmbedding h ((κ a).symm x, y))).val =
      firstBlockMatrixLinear F h x.val + blockDiagonalMatrixMap F h (0, (κ b y).val) := by
  rw [blockDiagonalEmbedding_coordinates, ContinuousMulEquiv.apply_symm_apply]
  change blockDiagonalMatrixMap F h (x.val, (κ b y).val) =
    blockDiagonalMatrixMap F h (x.val, 0) + blockDiagonalMatrixMap F h (0, (κ b y).val)
  rw [← map_add]
  simp

private theorem secondBlockCoordinates (x : G∞ a) (y : G b) :
    (κ n (blockDiagonalEmbedding h (x, (κ b).symm y))).val =
      secondBlockMatrixLinear F h y.val + blockDiagonalMatrixMap F h ((κ a x).val, 0) := by
  rw [blockDiagonalEmbedding_coordinates, ContinuousMulEquiv.apply_symm_apply]
  change blockDiagonalMatrixMap F h ((κ a x).val, y.val) =
    blockDiagonalMatrixMap F h (0, y.val) + blockDiagonalMatrixMap F h ((κ a x).val, 0)
  rw [← map_add]
  simp

private theorem affinePullbackExtension {k : ℕ} (i : G∞ k → G∞ n)
    (A : M k →L[ℝ] M n) (c : M n)
    (hi : ∀ x : G k, (κ n (i ((κ k).symm x))).val = A x.val + c)
    (f : SmoothFunctions F n) (x : G k) :
    coordinateExtension F n f (A x.val + c) = f.val (i ((κ k).symm x)) := by
  rw [← hi, coordinateExtension_apply, ContinuousMulEquiv.symm_apply_apply]

private def affineSmoothPullback {k : ℕ} (i : G∞ k → G∞ n)
    (A : M k →L[ℝ] M n) (c : M n)
    (hi : ∀ x : G k, (κ n (i ((κ k).symm x))).val = A x.val + c) :
    SmoothFunctions F n →ₗ[ℂ] SmoothFunctions F k where
  toFun f := ⟨f.val ∘ i, by
    intro x
    have hg := coordinateExtension_contDiffAt F n f (κ n (i ((κ k).symm x)))
    rw [hi] at hg
    have hA : ContMDiffAt 𝓘(ℝ, M k) 𝓘(ℝ, M n) ∞ (fun z : G k => A z.val + c) x :=
      (A.contDiff.add contDiff_const).comp_contMDiffAt (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) x)
    have hs : ContMDiffAt 𝓘(ℝ, M k) 𝓘(ℝ, ℂ) ∞
        (fun z : G k => coordinateExtension F n f (A z.val + c)) x :=
      hg.comp_contMDiffAt (f := fun z : G k => A z.val + c) hA
    exact hs.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z : G k => (affinePullbackExtension F i A c hi f z).symm)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem smoothDifferential_affineSmoothPullback {k : ℕ} (i : G∞ k → G∞ n)
    (A : M k →L[ℝ] M n) (c : M n)
    (hi : ∀ x : G k, (κ n (i ((κ k).symm x))).val = A x.val + c)
    (X : RealLieAlgebra F k) (Y : RealLieAlgebra F n)
    (ht : ∀ g : G∞ k, A ((κ k g).val * realLieAlgebraToMatrix F k X) =
      (κ n (i g)).val * realLieAlgebraToMatrix F n Y)
    (f : SmoothFunctions F n) (g : G∞ k) :
    (smoothDifferential F k X (affineSmoothPullback F i A c hi f)).val g =
      (smoothDifferential F n Y f).val (i g) := by
  let E (x : M k) := coordinateExtension F n f (A x + c)
  rw [smoothDifferential_eq_of_extension F k X _ E (affinePullbackExtension F i A c hi f),
    smoothDifferential_apply]
  have hx : A (κ k g).val + c = (κ n (i g)).val := by
    simpa only [ContinuousMulEquiv.symm_apply_apply] using (hi (κ k g)).symm
  have hD : HasFDerivAt (coordinateExtension F n f)
      (fderiv ℝ (coordinateExtension F n f) (κ n (i g)).val) (A (κ k g).val + c) := by
    rw [hx]
    exact ((coordinateExtension_contDiffAt F n f _).differentiableAt (by simp)).hasFDerivAt
  change fderiv ℝ (coordinateExtension F n f ∘ fun x : M k => A x + c) _ _ = _
  rw [(hD.comp (κ k g).val (A.hasFDerivAt.add_const c)).fderiv,
    ContinuousLinearMap.comp_apply, ht]

/-- Pullback of an infinite smooth function by holding the second block fixed. -/
def firstBlockSmoothPullback (y : G∞ b) : SmoothFunctions F n →ₗ[ℂ] SmoothFunctions F a :=
  affineSmoothPullback F (fun x => blockDiagonalEmbedding h (x, y))
    (firstBlockMatrixLinear F h) (blockDiagonalMatrixMap F h (0, (κ b y).val))
    (fun x => firstBlockCoordinates F h x y)

/-- Pullback of an infinite smooth function by holding the first block fixed. -/
def secondBlockSmoothPullback (x : G∞ a) : SmoothFunctions F n →ₗ[ℂ] SmoothFunctions F b :=
  affineSmoothPullback F (fun y => blockDiagonalEmbedding h (x, y))
    (secondBlockMatrixLinear F h) (blockDiagonalMatrixMap F h ((κ a x).val, 0))
    (fun y => secondBlockCoordinates F h x y)

@[simp]
theorem firstBlockSmoothPullback_apply (f : SmoothFunctions F n) (x : G∞ a) (y : G∞ b) :
    (firstBlockSmoothPullback F h y f).val x = f.val (blockDiagonalEmbedding h (x, y)) := rfl

@[simp]
theorem secondBlockSmoothPullback_apply (f : SmoothFunctions F n) (x : G∞ a) (y : G∞ b) :
    (secondBlockSmoothPullback F h x f).val y = f.val (blockDiagonalEmbedding h (x, y)) := rfl

/-- A first-block differential agrees with the derivative in its embedded direction. -/
theorem smoothDifferential_firstBlockSmoothPullback (X : RealLieAlgebra F a)
    (f : SmoothFunctions F n) (x : G∞ a) (y : G∞ b) :
    (smoothDifferential F a X (firstBlockSmoothPullback F h y f)).val x =
      (smoothDifferential F n (firstBlockRealLieInclusion F h X) f).val
        (blockDiagonalEmbedding h (x, y)) := by
  apply smoothDifferential_affineSmoothPullback
  intro g
  rw [blockDiagonalEmbedding_coordinates, firstBlockRealLieInclusion_matrix,
    ← blockDiagonalMatrixMap_mul]
  change blockDiagonalMatrixMap F h ((κ a g).val * realLieAlgebraToMatrix F a X, 0) =
    blockDiagonalMatrixMap F h ((κ a g).val * realLieAlgebraToMatrix F a X, (κ b y).val * 0)
  rw [mul_zero]

/-- A second-block differential agrees with the derivative in its embedded direction. -/
theorem smoothDifferential_secondBlockSmoothPullback (Y : RealLieAlgebra F b)
    (f : SmoothFunctions F n) (x : G∞ a) (y : G∞ b) :
    (smoothDifferential F b Y (secondBlockSmoothPullback F h x f)).val y =
      (smoothDifferential F n (secondBlockRealLieInclusion F h Y) f).val
        (blockDiagonalEmbedding h (x, y)) := by
  apply smoothDifferential_affineSmoothPullback
  intro g
  rw [blockDiagonalEmbedding_coordinates, secondBlockRealLieInclusion_matrix,
    ← blockDiagonalMatrixMap_mul]
  change blockDiagonalMatrixMap F h (0, (κ b g).val * realLieAlgebraToMatrix F b Y) =
    blockDiagonalMatrixMap F h ((κ a x).val * 0, (κ b g).val * realLieAlgebraToMatrix F b Y)
  rw [mul_zero]

end Langlands.Automorphic
