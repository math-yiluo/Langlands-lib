import Langlands.GroupScheme.Torus.HermitianLaurentOrthogonality
import Langlands.GroupScheme.Examples.SU3GroupScheme
import Langlands.GroupScheme.FiniteAlgebraWeilMatrixAffine

/-! # Actual tensor coefficients in Hermitian Laurent coordinates -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.HermitianLaurent

set_option backward.isDefEq.respectTransparency false

open SU3Root

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  (M : Type u) [AddCommMonoid M]

/-- The actual affine test scheme of the additive monoid algebra. -/
abbrev monoidAlgebraTest : Over (Spec (CommRingCat.of K)) :=
  (algSpec (CommRingCat.of K)).obj
    (op (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K M)))

/-- Affine global sections and scalar extension give Laurent coefficients. -/
def tensorCoefficients :
    L ⊗[K] ((algΓ (CommRingCat.of K)).obj
      (monoidAlgebraTest K M)).unop ≃ₐ[K]
      AddMonoidAlgebra L M :=
  (FiniteAlgebraUnits.WeilMatrixPoints.affineCoefficientEquiv K L
    (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K M))).trans
      ((AddMonoidAlgebra.scalarTensorEquiv K L).restrictScalars K)

@[simp] theorem tensorCoefficients_tmul
    (a : L) (s : SpecialLinear.WeilRoot.sectionAlgebra K (monoidAlgebraTest K M)) :
    tensorCoefficients K L M (a ⊗ₜ[K] s) =
      AddMonoidAlgebra.scalarTensorEquiv K L
        (a ⊗ₜ[K] (Corepresented.affineSectionsAlgEquiv
          (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K M))) s) := rfl

/-- Field coefficients become constant monomials. -/
@[simp] theorem tensorCoefficients_algebraMap (a : L) :
    tensorCoefficients K L M
      (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L
        (monoidAlgebraTest K M)) a) =
      AddMonoidAlgebra.single 0 a := by
  change AddMonoidAlgebra.scalarTensorEquiv K L
    (a ⊗ₜ[K] (Corepresented.affineSectionsAlgEquiv
      (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K M))) 1) = _
  rw [map_one]
  change AddMonoidAlgebra.scalarTensorEquiv K L
    (a ⊗ₜ[K] AddMonoidAlgebra.single 0 1) = _
  simpa only [AddMonoidAlgebra.scalarTensorEquiv_symm_single] using
    (AddMonoidAlgebra.scalarTensorEquiv K L (M := M)).apply_symm_apply
      (AddMonoidAlgebra.single 0 a)

variable {Idx : Type v}

/-- Scalar extension of the original Gram matrix becomes its constant Laurent matrix. -/
theorem tensorCoefficients_gram (J : Matrix Idx Idx L) :
    (J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L
      (monoidAlgebraTest K M)))).map (tensorCoefficients K L M) =
      J.map (AddMonoidAlgebra.single 0) := by
  funext i j
  exact tensorCoefficients_algebraMap K L M (J i j)

variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- The actual tensor conjugation becomes coefficientwise field conjugation. -/
theorem tensorCoefficients_bar
    (z : SpecialLinear.WeilRoot.tensorAlgebra K L (monoidAlgebraTest K M)) :
    tensorCoefficients K L M
      ((SU3Root.SchemeModel.coefficientInvolution K L (monoidAlgebraTest K M)).bar z) =
      (coefficientInvolution (M := M) (fieldInvolution K L)).bar
        (tensorCoefficients K L M z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a s =>
    change AddMonoidAlgebra.scalarTensorEquiv K L
        (conjugation K L a ⊗ₜ[K] (Corepresented.affineSectionsAlgEquiv
          (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K M))) s) =
      (coefficientInvolution (M := M) (fieldInvolution K L)).bar
        (AddMonoidAlgebra.scalarTensorEquiv K L
          (a ⊗ₜ[K] (Corepresented.affineSectionsAlgEquiv
            (CommAlgCat.of (CommRingCat.of K) (AddMonoidAlgebra K M))) s))
    ext m
    simp [AddMonoidAlgebra.scalarTensorEquiv_tmul, coefficientInvolution,
      AddMonoidAlgebra.coeff_mapAlgHom,
      fieldInvolution_bar, smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Fintype Idx]

/-- Full Gram preservation is retained in actual Laurent coordinates. -/
theorem tensorCoefficients_preservesGram
    (J : Matrix Idx Idx L)
    (P : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra K L
      (monoidAlgebraTest K M)))
    (hP : (P.map (SU3Root.SchemeModel.coefficientInvolution K L
        (monoidAlgebraTest K M)).bar).transpose *
      J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L
        (monoidAlgebraTest K M))) * P =
      J.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra K L
        (monoidAlgebraTest K M)))) :
    ((P.map (tensorCoefficients K L M)).map
      (coefficientInvolution (M := M) (fieldInvolution K L)).bar).transpose *
        J.map (AddMonoidAlgebra.single 0) * P.map (tensorCoefficients K L M) =
      J.map (AddMonoidAlgebra.single 0) := by
  have hbar :
      (P.map (SU3Root.SchemeModel.coefficientInvolution K L
        (monoidAlgebraTest K M)).bar).map (tensorCoefficients K L M) =
      (P.map (tensorCoefficients K L M)).map
        (coefficientInvolution (M := M) (fieldInvolution K L)).bar := by
    funext i j
    exact tensorCoefficients_bar K L M (P i j)
  have h := congrArg (fun Q => Q.map (tensorCoefficients K L M)) hP
  rw [Matrix.map_mul (f := tensorCoefficients K L M),
    Matrix.map_mul (f := tensorCoefficients K L M), Matrix.transpose_map, hbar,
    tensorCoefficients_gram] at h
  exact h

end Langlands.GroupScheme.HermitianLaurent
