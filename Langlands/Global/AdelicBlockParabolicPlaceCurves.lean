import Langlands.Global.ArchimedeanBlockParabolicCurves
import Langlands.Global.ArchimedeanPlaceRestriction
import Langlands.Global.AdelicBlockArchimedeanNormalization
import Langlands.Global.AdelicGLInverseTranspose

/-! # Single-place parabolic curves in mixed adelic coordinates -/

noncomputable section

open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 220000

universe u

namespace Langlands.Global.AdelicBlockParabolic

open Automorphic GeneralLinear NumberField ArchimedeanGL
open AdelicBlockDeterminantCharacter ArchimedeanCompactBlocks

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ
local notation "e" => archimedeanGLCoordinates F n

/-- Insert a real block-parabolic matrix at its real place in the infinite factor. -/
def realInfiniteParabolicInclusion (v : RP) : B.parabolic ℝ →* Infinite F B :=
  (infinite F B).toMonoidHom.comp (realPlaceInclusion F B v)

/-- Insert a complex block-parabolic matrix at its complex place in the infinite factor. -/
def complexInfiniteParabolicInclusion (v : CP) : B.parabolic ℂ →* Infinite F B :=
  (infinite F B).toMonoidHom.comp (complexPlaceInclusion F B v)

theorem ofInfinite_realInfiniteParabolicInclusion (v : RP) (p : B.parabolic ℝ) :
    ofInfinite F B (realInfiniteParabolicInclusion F B v p) = realPlaceInclusion F B v p := by
  have h := pair_projections F B (realPlaceInclusion F B v p)
  have hf : finite F B (realPlaceInclusion F B v p) = 1 := by
    apply Subtype.ext
    exact AdelicGL.finite_ofInfinite F n _
  rw [hf] at h
  exact h

theorem ofInfinite_complexInfiniteParabolicInclusion (v : CP) (p : B.parabolic ℂ) :
    ofInfinite F B (complexInfiniteParabolicInclusion F B v p) = complexPlaceInclusion F B v p := by
  have h := pair_projections F B (complexPlaceInclusion F B v p)
  have hf : finite F B (complexPlaceInclusion F B v p) = 1 := by
    apply Subtype.ext
    exact AdelicGL.finite_ofInfinite F n _
  rw [hf] at h
  exact h

private theorem coords_realInfiniteParabolicInclusion (v : RP) (p : B.parabolic ℝ) :
    (e (realInfiniteParabolicInclusion F B v p).val).val = realPlaceMatrix v p.val.val := by
  change (e (AdelicGL.infinite F n (AdelicGL.ofInfinite F n
    ((e).symm (RankinSelbergGlobal.realPlaceGL F n v p.val))))).val = _
  rw [AdelicGL.infinite_ofInfinite, ContinuousMulEquiv.apply_symm_apply, realPlaceGL_val]

private theorem coords_complexInfiniteParabolicInclusion (v : CP) (p : B.parabolic ℂ) :
    (e (complexInfiniteParabolicInclusion F B v p).val).val = complexPlaceMatrix v p.val.val := by
  change (e (AdelicGL.infinite F n (AdelicGL.ofInfinite F n
    ((e).symm (RankinSelbergGlobal.complexPlaceGL F n v p.val))))).val = _
  rw [AdelicGL.infinite_ofInfinite, ContinuousMulEquiv.apply_symm_apply, complexPlaceGL_val]

omit [NumberField F] in
private theorem realPlaceMatrix_affine (v : RP) (M : RM) :
    realPlaceMatrix v M = realPlaceMatrixBase v +
      realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v M) := by
  rw [realLieAlgebraToMatrix_realPlaceLieInclusion]
  refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (add_zero _).symm
  change (Pi.mulSingle v M : RP → RM) w i j =
    (if w = v then 0 else (1 : RM) i j) + (Pi.single v (M i j) : RP → ℝ) w
  by_cases h : w = v
  · subst w
    simp
  · simp [h]

omit [NumberField F] in
private theorem complexPlaceMatrix_affine (v : CP) (M : CM) :
    complexPlaceMatrix v M = complexPlaceMatrixBase v +
      realLieAlgebraToMatrix F n (complexPlaceLieInclusion F n v M) := by
  rw [realLieAlgebraToMatrix_complexPlaceLieInclusion]
  refine Matrix.ext fun i j => Prod.ext (add_zero _).symm (funext fun w => ?_)
  change (Pi.mulSingle v M : CP → CM) w i j =
    (if w = v then 0 else (1 : CM) i j) + (Pi.single v (M i j) : CP → ℂ) w
  by_cases h : w = v
  · subst w
    simp
  · simp [h]

/-- One-place differentiation gives the actual real Lie inclusion in the mixed matrix chart. -/
theorem realInfiniteParabolicInclusion_hasDerivAt (v : RP) (p : ℝ → B.parabolic ℝ) (X : RM)
    (hp : HasDerivAt (fun t => (p t).val.val) X 0) :
    HasDerivAt (fun t => (e (realInfiniteParabolicInclusion F B v (p t)).val).val)
      (realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v X)) 0 := by
  let L := ((realLieAlgebraToMatrix F n).toLinearMap ∘ₗ
    (realPlaceLieInclusion F n v).toLinearMap).toContinuousLinearMap
  have h := (L.hasFDerivAt.comp_hasDerivAt 0 hp).const_add (realPlaceMatrixBase v)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    (coords_realInfiniteParabolicInclusion F B v (p t)).trans (realPlaceMatrix_affine F v _))

/-- One-place differentiation gives the actual complex Lie inclusion in the mixed matrix chart. -/
theorem complexInfiniteParabolicInclusion_hasDerivAt (v : CP) (p : ℝ → B.parabolic ℂ) (X : CM)
    (hp : HasDerivAt (fun t => (p t).val.val) X 0) :
    HasDerivAt (fun t => (e (complexInfiniteParabolicInclusion F B v (p t)).val).val)
      (realLieAlgebraToMatrix F n (complexPlaceLieInclusion F n v X)) 0 := by
  let L := ((realLieAlgebraToMatrix F n).toLinearMap ∘ₗ
    (complexPlaceLieInclusion F n v).toLinearMap).toContinuousLinearMap
  have h := (L.hasFDerivAt.comp_hasDerivAt 0 hp).const_add (complexPlaceMatrixBase v)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    (coords_complexInfiniteParabolicInclusion F B v (p t)).trans (complexPlaceMatrix_affine F v _))

/-- Block extraction of the actual tangent is the real-place insertion of the local block. -/
theorem archimedeanDiagonalBlock_realPlaceLieInclusion (v : RP) (X : RM) (i : Fin B.length) :
    archimedeanDiagonalBlock F B i (realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v X)) =
      realLieAlgebraToMatrix F (B.size i)
        (realPlaceLieInclusion F (B.size i) v (localDiagonalBlock ℝ B i X)) := by
  rw [realLieAlgebraToMatrix_realPlaceLieInclusion, realLieAlgebraToMatrix_realPlaceLieInclusion]
  rfl

/-- Block extraction of the actual tangent is the complex-place insertion of the local block. -/
theorem archimedeanDiagonalBlock_complexPlaceLieInclusion (v : CP) (X : CM) (i : Fin B.length) :
    archimedeanDiagonalBlock F B i (realLieAlgebraToMatrix F n (complexPlaceLieInclusion F n v X)) =
      realLieAlgebraToMatrix F (B.size i)
        (complexPlaceLieInclusion F (B.size i) v (localDiagonalBlock ℂ B i X)) := by
  rw [realLieAlgebraToMatrix_complexPlaceLieInclusion, realLieAlgebraToMatrix_complexPlaceLieInclusion]
  rfl

theorem archimedeanHalfExtension_realInfiniteParabolicInclusion (v : RP) (p : B.parabolic ℝ) :
    archimedeanHalfExtension F B (e (realInfiniteParabolicInclusion F B v p).val).val =
      localLeviHalf ℝ B (B.leviProjection ℝ p) := by
  rw [archimedeanHalfExtension_parabolic, ofInfinite_realInfiniteParabolicInclusion,
    localLeviHalf_realPlace F B v p]

theorem archimedeanHalfExtension_complexInfiniteParabolicInclusion (v : CP) (p : B.parabolic ℂ) :
    archimedeanHalfExtension F B (e (complexInfiniteParabolicInclusion F B v p).val).val =
      localLeviHalf ℂ B (B.leviProjection ℂ p) := by
  rw [archimedeanHalfExtension_parabolic, ofInfinite_complexInfiniteParabolicInclusion,
    localLeviHalf_complexPlace F B v p]

/-- The derivative of the half-character extension through the identity in a Lie direction. -/
def archimedeanHalfDerivative (X : RealLieAlgebra F n) : ℂ :=
  fderiv ℝ (archimedeanHalfExtension F B) 1 (realLieAlgebraToMatrix F n X)

theorem archimedeanHalfExtension_hasDerivAt (p : ℝ → Infinite F B) (hp₀ : p 0 = 1)
    (X : RealLieAlgebra F n)
    (hp : HasDerivAt (fun t => (e (p t).val).val) (realLieAlgebraToMatrix F n X) 0) :
    HasDerivAt (fun t => archimedeanHalfExtension F B (e (p t).val).val)
      (archimedeanHalfDerivative F B X) 0 := by
  have hd : DifferentiableAt ℝ (archimedeanHalfExtension F B) 1 := by
    simpa only [OneMemClass.coe_one, map_one, Units.val_one] using
      (contDiffAt_archimedeanHalfExtension F B 1).differentiableAt (by simp)
  have h₀ : (e (p 0).val).val = 1 := by simp only [hp₀, OneMemClass.coe_one, map_one, Units.val_one]
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp h₀.symm

end Langlands.Global.AdelicBlockParabolic
