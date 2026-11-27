import Langlands.Global.InfiniteAdelicTangentKernelBijective
import Langlands.Geometry.Manifold.MatrixCoefficientLie
import Langlands.GroupScheme.GeneralLinearPointTopology
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Lie.AdjointTangentBracket

/-! # `X ↦ tangentKernel X` preserves Lie brackets

For a matrix representation `ρ` of `G`, the differential at the identity of the realization
`G(F_∞) → GL_n(F_∞)` is, entrywise, the derivative of the matrix coefficients of `ρ`, which is
the tangent matrix of `ρ` at `tangentKernel X`. The Library's `matrixDifferential_lie` says that
the left side carries Mathlib's bracket on the Lie algebra of `G(F_∞)` to the matrix commutator,
and `kernelDifferential_commutator` says the same of the right side for the Library's bracket on
the dual-number kernel. A faithful representation (`affineLinearEmbeddingStatement`) has an
injective tangent matrix map, so `tangentKernel` preserves brackets. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff Matrix

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

/-- The regular function on `G` giving the `(i, j)` entry of a matrix representation. -/
def representationEntry {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (i j : Fin n) :
    AffineCoordinateRing F G.X :=
  ρ.hom.hom.left.appTop (GeneralLinear.entrySection (Fin n) (CommRingCat.of F) i j)

omit [NumberField F] [IsAffine G.X.left] in
/-- The entries of a matrix representation at a point are the values of the entry functions. -/
theorem affineMatrix_apply_eq_evaluation {n : ℕ} (ρ : MatrixRepresentation G (Fin n))
    (C : CommAlgCat.{u} (CommRingCat.of F)) (g : G.affinePoints C) (i j : Fin n) :
    ((ρ.affineMatrix C g : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) i j =
      G.affinePointEvaluation C g (representationEntry F ρ i j) := by
  rw [MatrixRepresentation.affineMatrix_apply]
  exact GeneralLinear.affinePointsEquiv_entry_evaluation (Fin n) (CommRingCat.of F) C
    (g ≫ ρ.hom.hom) i j

/-- The realization of a matrix representation on `G(F_∞)`, with values in matrices over the
real normed algebra `Π_v F_v`. -/
def realization {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    InfiniteAdelicGroupPoints F G →* Matrix (Fin n) (Fin n) ((v : InfinitePlace F) → v.Completion)
    where
  toFun g := ((ρ.affineMatrix (CommAlgCat.of F (InfiniteAdeleRing F)) g :
    GL (Fin n) (InfiniteAdeleRing F)) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F))
  map_one' := by
    rw [map_one]
    rfl
  map_mul' g h := by
    rw [map_mul]
    rfl

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

theorem contMDiff_realization_entry {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (i j : Fin n) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, (v : InfinitePlace F) → v.Completion) ∞
      (fun g => realization F ρ g i j) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  refine contMDiff_pi_module_iff.mpr fun v => ?_
  have h := contMDiff_placeValue F hsmooth v (representationEntry F ρ i j)
  refine h.congr fun g => ?_
  change (((ρ.affineMatrix (CommAlgCat.of F (InfiniteAdeleRing F)) g :
    GL (Fin n) (InfiniteAdeleRing F)) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) i j) v = _
  rw [affineMatrix_apply_eq_evaluation]
  rfl

section Bracket

attribute [local instance] Lie.kernelLieRingOfField Lie.kernelLieAlgebraOfField

/-- The entrywise differential at the identity of the realization of `ρ` is the tangent matrix
of `ρ` at `tangentKernel X`. -/
theorem matrixDifferential_realization {n : ℕ} (ρ : MatrixRepresentation G (Fin n))
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    MatrixCoefficientLie.matrixDifferential 𝓘(ℝ, smoothModel F d) (realization F ρ) X =
      ρ.kernelDifferential (InfiniteAdeleRing F) (Additive.ofMul (tangentKernel F hsmooth X)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have : IsManifold 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothIsManifold F G hsmooth
  refine Matrix.ext fun i j => ?_
  funext v
  rw [MatrixCoefficientLie.matrixDifferential_apply]
  have hd : MDifferentiableAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, (v : InfinitePlace F) → v.Completion)
      (fun g => realization F ρ g i j) 1 :=
    (contMDiff_realization_entry F hsmooth ρ i j 1).mdifferentiableAt (by simp)
  have h1 := MatrixCoefficientLie.mvfderiv_clm_comp 𝓘(ℝ, smoothModel F d) hd
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun w : InfinitePlace F => w.Completion) v) X
  have hfun : (fun g => (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun w : InfinitePlace F => w.Completion) v) (realization F ρ g i j)) =
      placeValue F v (representationEntry F ρ i j) := by
    funext g
    change (((ρ.affineMatrix (CommAlgCat.of F (InfiniteAdeleRing F)) g :
      GL (Fin n) (InfiniteAdeleRing F)) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) i j) v = _
    rw [affineMatrix_apply_eq_evaluation]
    rfl
  rw [hfun] at h1
  change _ = (ρ.kernelDifferential (InfiniteAdeleRing F)
    (Additive.ofMul (tangentKernel F hsmooth X)) i j) v
  refine h1.symm.trans ?_
  have hm := Lie.affineMatrix_lieKernel_eq ρ (InfiniteAdeleRing F) (tangentKernel F hsmooth X)
  have he := affineMatrix_apply_eq_evaluation F ρ
    (CommAlgCat.of (CommRingCat.of F) (DualNumber (InfiniteAdeleRing F)))
    (tangentPoint F hsmooth X) i j
  have hs := affinePointEvaluation_tangentPoint_snd F hsmooth X (representationEntry F ρ i j)
  have hK : ρ.kernelDifferential (InfiniteAdeleRing F)
      (Additive.ofMul (tangentKernel F hsmooth X)) i j =
        regularDerivative F hsmooth X (representationEntry F ρ i j) := by
    rw [MatrixRepresentation.kernelDifferential_apply]
    change (ρ.tangentMatrix (InfiniteAdeleRing F) (tangentKernel F hsmooth X)) i j = _
    have h2 := congrArg (fun M : GL (Fin n) (DualNumber (InfiniteAdeleRing F)) =>
      ((M : Matrix (Fin n) (Fin n) (DualNumber (InfiniteAdeleRing F))) i j).snd) hm
    simp only [GeneralLinear.DualNumber.matrixUnit_val, Matrix.add_apply,
      TrivSqZeroExt.snd_add] at h2
    rw [← hs, ← he]
    refine Eq.trans ?_ h2.symm
    simp [GeneralLinear.DualNumber.epsilonMatrix, Matrix.one_apply]
    split_ifs <;> simp
  rw [hK]
  rfl

/-- `X ↦ tangentKernel X` carries Mathlib's bracket on the Lie algebra of `G(F_∞)` to the
Library's bracket on the dual-number kernel of `G` over `F_∞`. -/
theorem tangentKernel_lie
    (X Y : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
      LieGroup.of_le (n := ∞) (by simp)
    Additive.ofMul (tangentKernel F hsmooth ⁅X, Y⁆) =
      ⁅Additive.ofMul (tangentKernel F hsmooth X), Additive.ofMul (tangentKernel F hsmooth Y)⁆ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  have : SmoothOfRelativeDimension d G.X.hom := hsmooth
  have : Smooth G.X.hom := SmoothOfRelativeDimension.smooth d G.X.hom
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement F G inferInstance inferInstance
  apply Lie.kernelDifferential_injective (A := InfiniteAdeleRing F) ρ hρ.mono_overHom
  rw [MatrixRepresentation.kernelDifferential_commutator,
    ← matrixDifferential_realization F hsmooth ρ, ← matrixDifferential_realization F hsmooth ρ X,
    ← matrixDifferential_realization F hsmooth ρ Y]
  exact MatrixCoefficientLie.matrixDifferential_lie (realization F ρ)
    (contMDiff_realization_entry F hsmooth ρ) X Y

end Bracket

end Langlands.Global.InfiniteAdelicGroupPoints
