import Langlands.GroupScheme.Torus.HermitianLaurentTensorCoefficients
import Langlands.GroupScheme.Torus.FiniteMatrixHermitianWeightBound

/-! # The actual Hermitian universal Laurent matrix -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open FiniteAlgebraUnits HermitianLaurent

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {N d : ℕ} (b : Module.Basis (Fin d) K (Matrix (Fin N) (Fin N) L))
  {M : Type u} [AddCommMonoid M]

/-- Actual all-test matrices recover the scalar-extended Laurent matrix. -/
theorem map_tensorCoefficients_tensorMatrixEquiv
    (x : monoidAlgebraTest K M ⟶ (groupScheme b).X) :
    (WeilMatrixPoints.tensorMatrixEquiv K L b _ x : Matrix (Fin N) (Fin N)
      (SpecialLinear.WeilRoot.tensorAlgebra K L (monoidAlgebraTest K M))).map
        (tensorCoefficients K L M) =
      laurentMatrixEquiv K L (M := M) (N := N)
        (affinePointsEquiv b (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K M)) x) := by
  change ((WeilMatrixPoints.tensorMatrixEquiv K L b _ x : Matrix (Fin N) (Fin N)
      (SpecialLinear.WeilRoot.tensorAlgebra K L (monoidAlgebraTest K M))).map
        (WeilMatrixPoints.affineCoefficientEquiv K L
          (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K M)))).map
          (AddMonoidAlgebra.scalarTensorEquiv K L) = _
  rw [WeilMatrixPoints.map_affineCoefficientEquiv_tensorMatrixEquiv]
  rfl

variable {K L b} {I : Type u} [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of K)) I ⟶ groupScheme b)

/-- The actual tensor-coefficient matrix of the inverse universal point. -/
def inverseUniversalTensorMatrix : Matrix.GeneralLinearGroup (Fin N)
    (SpecialLinear.WeilRoot.tensorAlgebra K L (monoidAlgebraTest K (I → ℤ))) :=
  WeilMatrixPoints.tensorMatrixEquiv K L b _
    ((splitTorus.universalPoint (R := CommRingCat.of K) I ≫ i.hom.hom)⁻¹)

/-- The inverse universal matrix comes from the inverse of the actual universal point. -/
theorem inverseUniversalMatrix_eq_map_tensor :
    (inverseUniversalMatrix i : Matrix (Fin N) (Fin N) (AddMonoidAlgebra L (I → ℤ))) =
      (inverseUniversalTensorMatrix i : Matrix (Fin N) (Fin N)
        (SpecialLinear.WeilRoot.tensorAlgebra K L
          (monoidAlgebraTest K (I → ℤ)))).map (tensorCoefficients K L (I → ℤ)) := by
  unfold inverseUniversalTensorMatrix
  rw [map_tensorCoefficients_tensorMatrixEquiv]
  change laurentMatrixEquiv K L (M := I → ℤ) (N := N)
    (↑((FiniteAlgebraTorusWeights.universalUnit i)⁻¹) :
      AddMonoidAlgebra K (I → ℤ) ⊗[K] Matrix (Fin N) (Fin N) L) = _
  rw [map_inv]
  rfl

variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- All-test full Gram preservation gives preservation by the inverse Laurent matrix. -/
theorem inverseUniversalMatrix_preservesGram
    (J : Matrix (Fin N) (Fin N) L)
    (hJ : ∀ (T : Over (Spec (CommRingCat.of K)))
      (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X),
      ((WeilMatrixPoints.tensorMatrixEquiv K L b T (x ≫ i.hom.hom) :
        Matrix (Fin N) (Fin N) (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
          (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
        J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
        (WeilMatrixPoints.tensorMatrixEquiv K L b T (x ≫ i.hom.hom) :
          Matrix (Fin N) (Fin N) (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
        J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T))) :
    ((inverseUniversalMatrix i : Matrix (Fin N) (Fin N)
      (AddMonoidAlgebra L (I → ℤ))).map
        (coefficientInvolution (SU3Root.fieldInvolution K L)).bar).transpose *
      J.map (AddMonoidAlgebra.single 0) *
      (inverseUniversalMatrix i : Matrix (Fin N) (Fin N)
        (AddMonoidAlgebra L (I → ℤ))) = J.map (AddMonoidAlgebra.single 0) := by
  rw [inverseUniversalMatrix_eq_map_tensor]
  apply tensorCoefficients_preservesGram
  unfold inverseUniversalTensorMatrix
  rw [← GrpObj.inv_comp]
  exact hJ _ _

/-- A faithful all-test Hermitian matrix torus has rank at most the attained Witt index. -/
theorem card_le_wittIndex_of_allTest_isometry
    (hi : Mono i.hom.hom.left)
    (H : HermitianMatrix.Form (SU3Root.fieldInvolution K L) (Fin N))
    (hH : ∀ (T : Over (Spec (CommRingCat.of K)))
      (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X),
      ((WeilMatrixPoints.tensorMatrixEquiv K L b T (x ≫ i.hom.hom) :
        Matrix (Fin N) (Fin N) (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
          (SU3Root.SchemeModel.coefficientInvolution K L T).bar).transpose *
        (H.gram : Matrix (Fin N) (Fin N) L).map
          (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T)) *
        (WeilMatrixPoints.tensorMatrixEquiv K L b T (x ≫ i.hom.hom) :
          Matrix (Fin N) (Fin N) (SpecialLinear.WeilRoot.tensorAlgebra K L T)) =
        (H.gram : Matrix (Fin N) (Fin N) L).map
          (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L T))) :
    Fintype.card I ≤ H.wittIndex :=
  card_le_wittIndex_of_inverseUniversalMatrix_isometry i hi _ H
    (inverseUniversalMatrix_preservesGram i _ hH)

end Langlands.GroupScheme.FiniteMatrixAlgebraTorusWeights
