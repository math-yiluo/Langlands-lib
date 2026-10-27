import Langlands.Global.ArchimedeanRelativeAdjoint

/-! # Equivariant Lie retraction onto the actual reduced archimedean algebra -/

noncomputable section

universe u

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

@[simp]
theorem splitCenterCoordinate_reduced (X : reducedLieSubalgebra K n) :
    splitCenterCoordinate K n X = 0 := by
  change (n : ℝ)⁻¹ • realTrace K n X = 0
  rw [X.property, smul_zero]

@[simp]
theorem reducedProjection_reduced [NeZero n] (X : reducedLieSubalgebra K n) :
    reducedProjection K n X = X := by
  apply Subtype.ext
  simp only [reducedProjection_apply, splitCenterCoordinate_reduced, map_zero, sub_zero]

theorem reducedProjection_lie [NeZero n] (X Y : RealLieAlgebra K n) :
    reducedProjection K n ⁅X, Y⁆ =
      ⁅reducedProjection K n X, reducedProjection K n Y⁆ := by
  apply Subtype.ext
  change (reducedProjection K n ⁅X, Y⁆ : RealLieAlgebra K n) =
    ⁅(reducedProjection K n X : RealLieAlgebra K n),
      (reducedProjection K n Y : RealLieAlgebra K n)⁆
  simp only [reducedProjection_apply]
  have htrace : splitCenterCoordinate K n ⁅X, Y⁆ = 0 := by
    change (n : ℝ)⁻¹ • realTrace K n ⁅X, Y⁆ = 0
    rw [realTrace_lie, smul_zero]
  have hcentral :
      ⁅X, splitCenterScalar K n (splitCenterCoordinate K n Y)⁆ = 0 := by
    rw [← lie_skew, splitCenterScalar_lie, neg_zero]
  rw [htrace, map_zero, sub_zero, lie_sub, sub_lie, sub_lie,
    splitCenterScalar_lie, splitCenterScalar_lie, hcentral]
  simp

/-- The normalized real-trace projection preserves the actual matrix Lie bracket. -/
def reducedLieProjection [NeZero n] :
    RealLieAlgebra K n →ₗ⁅ℝ⁆ reducedLieSubalgebra K n :=
  { reducedProjection K n with
    map_lie' := by
      intro X Y
      exact reducedProjection_lie K n X Y }

@[simp]
theorem reducedLieProjection_apply [NeZero n] (X : RealLieAlgebra K n) :
    reducedLieProjection K n X = reducedProjection K n X := rfl

/-- Real scalar matrices are fixed by every actual infinite adelic conjugation. -/
theorem realLieConjugation_splitCenterScalar (g : InfiniteAdelicGL K n)
    (r : SplitCenterCoordinates K) :
    realLieConjugation K n g (splitCenterScalar K n r) = splitCenterScalar K n r := by
  apply (realLieAlgebraToMatrix K n).injective
  simp only [realLieAlgebraToMatrix_realLieConjugation, splitCenterScalar_matrix, map_inv]
  rw [← (Matrix.scalar_commute _ (Commute.all _) _).eq, mul_assoc]
  simp

/-- The real trace retraction commutes with the actual full adjoint action. -/
theorem reducedProjection_conjugation [NeZero n] (g : InfiniteAdelicGL K n)
    (X : RealLieAlgebra K n) :
    reducedProjection K n (realLieConjugation K n g X) =
      reducedRealLieConjugation K n g (reducedProjection K n X) := by
  apply Subtype.ext
  rw [reducedProjection_apply, reducedRealLieConjugation_coe,
    reducedProjection_apply, map_sub, realLieConjugation_splitCenterScalar]
  have ht : splitCenterCoordinate K n (realLieConjugation K n g X) =
      splitCenterCoordinate K n X := by
    simp only [splitCenterCoordinate, LinearMap.smul_apply, realTrace_realLieConjugation]
  rw [ht]

/-- Complexified retraction onto the reduced algebra, obtained by scalar extension. -/
def reducedComplexProjection [NeZero n] :
    ComplexLieAlgebra K n →ₗ⁅ℂ⁆ ReducedComplexLieAlgebra K n :=
  { (reducedLieProjection K n).toLinearMap.baseChange ℂ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (reducedLieProjection K n)).map_lie X Y }

@[simp]
theorem reducedComplexProjection_tmul [NeZero n] (z : ℂ) (X : RealLieAlgebra K n) :
    reducedComplexProjection K n (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] reducedProjection K n X := rfl

@[simp]
theorem reducedComplexProjection_inclusion [NeZero n]
    (X : ReducedComplexLieAlgebra K n) :
    reducedComplexProjection K n (reducedComplexInclusion K n X) = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [reducedComplexInclusion_tmul, reducedComplexProjection_tmul,
      reducedProjection_reduced]
  | add X Y hX hY => simp only [map_add, hX, hY]

theorem reducedComplexProjection_surjective [NeZero n] :
    Function.Surjective (reducedComplexProjection K n) :=
  fun X => ⟨reducedComplexInclusion K n X, reducedComplexProjection_inclusion K n X⟩

@[simp]
theorem reducedComplexProjection_compact [NeZero n] (Y : CompactComplexLieAlgebra K n) :
    reducedComplexProjection K n (compactComplexInclusion K n Y) =
      compactToReducedComplex K n Y := by
  rw [← reducedComplexInclusion_compact, reducedComplexProjection_inclusion]

/-- Scalar extension retains equivariance for all infinite adelic elements. -/
theorem reducedComplexProjection_conjugation [NeZero n] (g : InfiniteAdelicGL K n)
    (X : ComplexLieAlgebra K n) :
    reducedComplexProjection K n (complexLieConjugation K n g X) =
      reducedComplexLieConjugation K n g (reducedComplexProjection K n X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexLieConjugation_tmul, reducedComplexProjection_tmul,
      reducedComplexLieConjugation_tmul, reducedProjection_conjugation]
  | add X Y hX hY => simp only [map_add, hX, hY]

end Langlands.Global.ArchimedeanGL
