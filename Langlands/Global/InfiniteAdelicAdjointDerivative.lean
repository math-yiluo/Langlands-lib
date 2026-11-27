import Langlands.Global.InfiniteAdelicCharacterDerivative
import Langlands.Algebra.DualNumberDeterminant
import Langlands.GroupScheme.Lie.AdjointDeterminantCharacter
import Langlands.GroupScheme.Lie.AdjointTangentBracket

/-! # The derivative of the adjoint determinant along an identity tangent vector of `G(F_∞)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- For a morphism `j : G ⟶ P` and a tangent vector `X` at the identity of `G(F_∞)`, the matrix
of `ε`-coefficients of `Ad_P` at the image under `j` of the dual-number point of `X`, in the
Library's finite coordinates of the Lie algebra of `P`. -/
def adjointTangentMatrix {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
    [LocallyOfFiniteType P.X.hom] (j : G ⟶ P)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    Matrix (Fin (Module.finrank F (Additive (lieKernel P F))))
      (Fin (Module.finrank F (Additive (lieKernel P F)))) (InfiniteAdeleRing F) :=
  ((AutomorphicAction.conjugation (𝟙 P)).coordinateMatrix (Lie.finiteCoordinates P)
      (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
      (tangentPoint F hsmooth X ≫ j.hom.hom)).val.map
    (TrivSqZeroExt.snd : DualNumber (InfiniteAdeleRing F) → InfiniteAdeleRing F)

set_option maxRecDepth 8192 in
/-- The derivative along `X` of `det Ad_P ∘ j` is the trace of `adjointTangentMatrix`. -/
theorem regularDerivative_adjointDeterminant {P : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] (j : G ⟶ P)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    regularDerivative F hsmooth X (characterRegularFunction F G
        (characterRestrict j (Lie.adjointDeterminantCharacter P))) =
      Matrix.trace (adjointTangentMatrix F hsmooth j X) := by
  let A := CommAlgCat.of F (DualNumber (InfiniteAdeleRing F))
  let g : P.affinePoints A := tangentPoint F hsmooth X ≫ j.hom.hom
  let a := AutomorphicAction.conjugation (𝟙 P)
  let c := Lie.finiteCoordinates P
  have hval := characterUnits_val_eq_evaluation F G
    (characterRestrict j (Lie.adjointDeterminantCharacter P)) A (tangentPoint F hsmooth X)
  have hsnd := affinePointEvaluation_tangentPoint_snd F hsmooth X
    (characterRegularFunction F G (characterRestrict j (Lie.adjointDeterminantCharacter P)))
  have hunits : characterUnits F G
      (characterRestrict j (Lie.adjointDeterminantCharacter P)).toMul A
        (tangentPoint F hsmooth X) = LinearEquiv.det (a.differential g) :=
    Lie.adjointDeterminantCharacter_affinePoints P A g
  have hred : P.affinePointMap (CommAlgCat.ofHom
      (TrivSqZeroExt.fstHom F (InfiniteAdeleRing F) (InfiniteAdeleRing F))) g = 1 := by
    change (Lie.reduction G (tangentPoint F hsmooth X)) ≫ j.hom.hom = 1
    rw [reduction_tangentPoint]
    exact map_one (G.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)))
  have hfst : ((a.coordinateMatrix c A g).val).map
      (TrivSqZeroExt.fst : DualNumber (InfiniteAdeleRing F) → InfiniteAdeleRing F) = 1 := by
    have hnat := a.coordinateMatrix_naturality c (CommAlgCat.ofHom
      (TrivSqZeroExt.fstHom F (InfiniteAdeleRing F) (InfiniteAdeleRing F))) g
    rw [hred, map_one] at hnat
    ext i k
    have h := congrArg (fun M : GL (Fin (Module.finrank F (Additive (lieKernel P F))))
      (InfiniteAdeleRing F) => M.val i k) hnat
    simp only [Matrix.GeneralLinearGroup.map_apply] at h
    rw [Matrix.map_apply]
    exact h.symm.trans (by simp)
  have hdet := Langlands.Algebra.DualNumberDeterminant.det_eq_of_map_fst_eq_one _ hfst
  have hd := a.coordinateMatrix_det c A g
  have key : ((LinearEquiv.det (a.differential g)).val : DualNumber (InfiniteAdeleRing F)) =
      ((a.coordinateMatrix c A g).val).det := by
    rw [← hd, Matrix.GeneralLinearGroup.val_det_apply]
  calc regularDerivative F hsmooth X (characterRegularFunction F G
        (characterRestrict j (Lie.adjointDeterminantCharacter P)))
      = ((characterUnits F G (characterRestrict j (Lie.adjointDeterminantCharacter P)).toMul A
          (tangentPoint F hsmooth X)).val : DualNumber (InfiniteAdeleRing F)).snd := by
        rw [hval]
        exact hsnd.symm
    _ = ((LinearEquiv.det (a.differential g)).val : DualNumber (InfiniteAdeleRing F)).snd := by
        rw [hunits]
    _ = (((a.coordinateMatrix c A g).val).det : DualNumber (InfiniteAdeleRing F)).snd := by
        rw [key]
    _ = Matrix.trace (adjointTangentMatrix F hsmooth j X) := by
        rw [hdet, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
        unfold adjointTangentMatrix
        rfl

/-- The derivative at the identity of the normalizing factor `m ↦ δ_P(j(m))^{-1/2}` along `X`
is `-1/2 · Σ_v mult(v) · Re(tr N_X)_v`, where `N_X = adjointTangentMatrix j X` is the matrix of
`ε`-coefficients of `Ad_P` at the image of the dual-number point of `X`. -/
theorem mfderiv_halfModulus_one_eq_trace {P : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] (j : G ⟶ P)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ)
        (fun m => parameterPower F P (-halfModulusParameter F P)
          (map F G P j (ofInfinite F G m))) 1 X =
      (-1 / 2 : ℂ) * ((∑ v : InfinitePlace F, (v.mult : ℝ) *
        RCLike.re (Matrix.trace (adjointTangentMatrix F hsmooth j X) v) : ℝ) : ℂ) := by
  rw [mfderiv_halfModulus_one, regularDerivative_adjointDeterminant]

section Bracket

attribute [local instance] Lie.kernelLieRingOfField Lie.kernelLieAlgebraOfField

set_option maxRecDepth 8192 in
/-- `adjointTangentMatrix j X` is the tangent matrix of the coordinate adjoint representation of
`P` at the image under `Lie j` of the dual-number kernel element of `X`. -/
theorem adjointTangentMatrix_eq_kernelDifferential {P : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] (j : G ⟶ P)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    adjointTangentMatrix F hsmooth j X =
      (Lie.adjointRepresentation (Lie.finiteCoordinates P)).kernelDifferential
        (InfiniteAdeleRing F)
        (Lie.targetMapLinear j (InfiniteAdeleRing F) (Additive.ofMul (tangentKernel F hsmooth X))) :=
  Lie.coordinateMatrix_conjugation_snd (Lie.finiteCoordinates P) (InfiniteAdeleRing F)
    (Lie.targetMap j (InfiniteAdeleRing F) (tangentKernel F hsmooth X))

/-- The trace of `adjointTangentMatrix j X` is the trace over `F_∞` of `ad (Lie j (B X))` on the
Lie algebra of `P` over `F_∞`, where `B X = tangentKernel X`. -/
theorem trace_adjointTangentMatrix {P : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] (j : G ⟶ P)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    Matrix.trace (adjointTangentMatrix F hsmooth j X) =
      LinearMap.trace (InfiniteAdeleRing F) (Additive (lieKernel P (InfiniteAdeleRing F)))
        (LieModule.toEnd (InfiniteAdeleRing F) (Additive (lieKernel P (InfiniteAdeleRing F)))
          (Additive (lieKernel P (InfiniteAdeleRing F)))
          (Lie.targetMapLinear j (InfiniteAdeleRing F)
            (Additive.ofMul (tangentKernel F hsmooth X)))) := by
  rw [adjointTangentMatrix_eq_kernelDifferential,
    Lie.trace_toEnd_eq_trace_kernelDifferential (Lie.finiteCoordinates P)]

/-- The derivative at the identity of the normalizing factor `m ↦ δ_P(j(m))^{-1/2}` along `X`
is `-1/2 · Σ_v mult(v) · Re(tr_{F_∞}(ad (Lie j (B X))))_v`, the trace being that of the adjoint
action on the Lie algebra of `P` over `F_∞`. -/
theorem mfderiv_halfModulus_one_eq_trace_ad {P : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] (j : G ⟶ P)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ)
        (fun m => parameterPower F P (-halfModulusParameter F P)
          (map F G P j (ofInfinite F G m))) 1 X =
      (-1 / 2 : ℂ) * ((∑ v : InfinitePlace F, (v.mult : ℝ) *
        RCLike.re (LinearMap.trace (InfiniteAdeleRing F)
          (Additive (lieKernel P (InfiniteAdeleRing F)))
          (LieModule.toEnd (InfiniteAdeleRing F) (Additive (lieKernel P (InfiniteAdeleRing F)))
            (Additive (lieKernel P (InfiniteAdeleRing F)))
            (Lie.targetMapLinear j (InfiniteAdeleRing F)
              (Additive.ofMul (tangentKernel F hsmooth X)))) v) : ℝ) : ℂ) := by
  rw [mfderiv_halfModulus_one_eq_trace, trace_adjointTangentMatrix]

end Bracket

end Langlands.Global.InfiniteAdelicGroupPoints
