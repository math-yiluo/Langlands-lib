import Langlands.GroupScheme.FiniteAlgebraWeilMatrixPoints
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Affine comparison for finite matrix algebra points -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.FiniteAlgebraUnits.WeilMatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {N d : ℕ} (b : Module.Basis (Fin d) K (Matrix (Fin N) (Fin N) L))

/-- Transport actual affine global sections to the original coefficient algebra. -/
def affineCoefficientEquiv (R : CommAlgCat.{u} (CommRingCat.of K)) :
    L ⊗[K] ((algΓ (CommRingCat.of K)).obj
      ((algSpec (CommRingCat.of K)).obj (op R))).unop ≃ₐ[K] L ⊗[K] R :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[K] L)
    (Corepresented.affineSectionsAlgEquiv R)

/-- The affine comparison commutes with swapping the coefficient tensor factors. -/
theorem affineCoefficientEquiv_comm (R : CommAlgCat.{u} (CommRingCat.of K))
    (z : ((algΓ (CommRingCat.of K)).obj
      ((algSpec (CommRingCat.of K)).obj (op R))).unop ⊗[K] L) :
    affineCoefficientEquiv K L R (Algebra.TensorProduct.comm K _ L z) =
      Algebra.TensorProduct.comm K R L
        (Algebra.TensorProduct.map (Corepresented.affineSectionsIso R).hom.hom
          (AlgHom.id K L) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r l => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- All-test matrix coordinates on an affine test recover the affine matrix coordinates. -/
theorem map_affineCoefficientEquiv_tensorMatrixEquiv
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (x : (algSpec (CommRingCat.of K)).obj (op R) ⟶ (groupScheme b).X) :
    (tensorMatrixEquiv K L b _ x : Matrix (Fin N) (Fin N)
      (SpecialLinear.WeilRoot.tensorAlgebra K L
        ((algSpec (CommRingCat.of K)).obj (op R)))).map
        (affineCoefficientEquiv K L R) =
      (MatrixPoints.affineMatrixEquiv K L b R x : Matrix (Fin N) (Fin N) (R ⊗[K] L)).map
        (Algebra.TensorProduct.comm K R L) := by
  have hp := Corepresented.map_affineSectionsIso_pointsEquiv
    (functor K (Matrix (Fin N) (Fin N) L)) (corepresentableBy b) R x
  change Units.map
    (Algebra.TensorProduct.map (Corepresented.affineSectionsIso R).hom.hom
      (AlgHom.id K (Matrix (Fin N) (Fin N) L))).toMonoidHom
      (pointsEquiv b _ x) = affinePointsEquiv b R x at hp
  change ((MatrixPoints.coefficientEquiv K L _ (pointsEquiv b _ x :
    _ ⊗[K] Matrix (Fin N) (Fin N) L)).map (Algebra.TensorProduct.comm K _ L)).map
      (affineCoefficientEquiv K L R) = _
  have hn := MatrixPoints.coefficientEquiv_naturality K L
    (Corepresented.affineSectionsIso R).hom.hom
    (pointsEquiv b _ x : _ ⊗[K] Matrix (Fin N) (Fin N) L)
  have hpv := congrArg Units.val hp
  change Algebra.TensorProduct.map (Corepresented.affineSectionsIso R).hom.hom
    (AlgHom.id K (Matrix (Fin N) (Fin N) L)) (pointsEquiv b _ x :
      _ ⊗[K] Matrix (Fin N) (Fin N) L) =
    (affinePointsEquiv b R x : R ⊗[K] Matrix (Fin N) (Fin N) L) at hpv
  rw [hpv] at hn
  funext r c
  change affineCoefficientEquiv K L R
    (Algebra.TensorProduct.comm K _ L
      (MatrixPoints.coefficientEquiv K L _ (pointsEquiv b _ x) r c)) = _
  rw [affineCoefficientEquiv_comm]
  exact congrArg (fun P : Matrix (Fin N) (Fin N) (R ⊗[K] L) =>
    Algebra.TensorProduct.comm K R L (P r c)) hn.symm

end Langlands.GroupScheme.FiniteAlgebraUnits.WeilMatrixPoints
