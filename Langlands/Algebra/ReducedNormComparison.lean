import Langlands.Algebra.ReducedNormEvaluation
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Comparison of the descended law with every splitting field and chart. -/

noncomputable section

namespace Langlands.ReducedNorm

universe uK uL uA uI uJ uE uF uR

open scoped TensorProduct
open MvPolynomial

variable {K : Type uK} [Field K] {A : Type uA} [Ring A] [Algebra K A]
  {L : Type uL} [Field L] [Algebra K L]
  {I : Type uI} [Fintype I] [DecidableEq I]
  {J : Type uJ} [Fintype J]

/-- Scalar extension of a splitting chart is an actual algebra equivalence. -/
def extendSplittingChart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (E : Type uE) [CommRing E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] :
    E ⊗[K] A ≃ₐ[E] Matrix I I E := by
  let c : E ⊗[K] A ≃ₗ[L] Matrix I I E :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L L E A).symm.trans
      (TensorProduct.congr (LinearEquiv.refl L E) e.toLinearEquiv)).trans
      (matrixEquivTensor I L E).symm.toLinearEquiv
  have hc : (splittingMap e E : E ⊗[K] A → Matrix I I E) = c := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul r a => simp [c, splittingMap_tmul, matrixEquivTensor_apply_symm]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact AlgEquiv.ofBijective (splittingMap e E) (hc ▸ c.bijective)

@[simp] theorem extendSplittingChart_apply (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (E : Type uE) [CommRing E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    (x : E ⊗[K] A) : extendSplittingChart e E x = splittingMap e E x := rfl

/-- The actual determinant coordinate polynomial commutes with extension of a chart. -/
theorem chartPolynomial_baseChange (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (E : Type uE) [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    (a : J → A) :
    MvPolynomial.map (algebraMap L E) (chartPolynomial e (fun j => 1 ⊗ₜ[K] a j)) =
      chartPolynomial (extendSplittingChart e E) (fun j => 1 ⊗ₜ[K] a j) := by
  simp only [chartPolynomial, detPolynomial_map, extendSplittingChart_apply,
    splittingMap_tmul, one_smul]

section Comparison

variable [Nonempty I] [FiniteDimensional K L] [IsGalois K L]
  {F : Type uF} [Field F] [Algebra K F]

/-- Compare coefficients in a common overfield and reflect them to the arbitrary splitting field. -/
theorem descendedPolynomial_map_common (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (f : F ⊗[K] A ≃ₐ[F] Matrix I I F) (a : J → A)
    (E : Type uE) [Field E] [Algebra K E] [Algebra L E] [Algebra F E]
    [IsScalarTower K L E] [IsScalarTower K F E] :
    MvPolynomial.map (algebraMap K F) (descendedPolynomial e a) =
      chartPolynomial f (fun j => 1 ⊗ₜ[K] a j) := by
  apply MvPolynomial.map_injective (algebraMap F E)
    (FaithfulSMul.algebraMap_injective F E)
  rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq K F E,
    IsScalarTower.algebraMap_eq K L E, ← MvPolynomial.map_map,
    descendedPolynomial_map, chartPolynomial_baseChange, chartPolynomial_baseChange]
  exact chartPolynomial_independent (extendSplittingChart f E) (extendSplittingChart e E) _

/-- Every splitting field and chart yields the same determinant polynomial after coefficient extension. -/
theorem descendedPolynomial_map_chart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (f : F ⊗[K] A ≃ₐ[F] Matrix I I F) (a : J → A) :
    MvPolynomial.map (algebraMap K F) (descendedPolynomial e a) =
      chartPolynomial f (fun j => 1 ⊗ₜ[K] a j) := by
  let emb : L →ₐ[K] AlgebraicClosure F := IsAlgClosed.lift
  let : Algebra L (AlgebraicClosure F) := emb.toRingHom.toAlgebra
  let : IsScalarTower K L (AlgebraicClosure F) := IsScalarTower.of_algHom emb
  exact descendedPolynomial_map_common e f a (AlgebraicClosure F)

/-- Determinant comparison under every splitting chart, over every further commutative test algebra. -/
theorem normFromGalois_eq_det_of_chart (b : Module.Basis J K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (f : F ⊗[K] A ≃ₐ[F] Matrix I I F)
    (R : Type uR) [CommRing R] [Algebra K R] [Algebra F R] [IsScalarTower K F R]
    (x : R ⊗[K] A) : normFromGalois b e R x = (splittingMap f R x).det := by
  change polynomialValue b (descendedPolynomial e b) R x = _
  unfold polynomialValue
  rw [IsScalarTower.algebraMap_eq K F R, ← MvPolynomial.eval₂_map,
    descendedPolynomial_map_chart e f, chartPolynomial, detPolynomial_eval]
  congr 1
  calc
    _ = splittingMap f R (∑ j, (b.baseChange R).repr x j ⊗ₜ[K] b j) := by
      rw [map_sum]
      rfl
    _ = splittingMap f R x := congrArg (splittingMap f R) (sum_coordinates_tmul b R x)

variable [FiniteDimensional K F] [IsGalois K F]

/-- The descended polynomial is independent of the finite Galois splitting field and chart. -/
theorem descendedPolynomial_splitting_independent
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (f : F ⊗[K] A ≃ₐ[F] Matrix I I F)
    (a : J → A) : descendedPolynomial f a = descendedPolynomial e a := by
  apply MvPolynomial.map_injective (algebraMap K F)
    (FaithfulSMul.algebraMap_injective K F)
  rw [descendedPolynomial_map, descendedPolynomial_map_chart e f]

/-- The all-test law is independent of both splitting choices and coordinates. -/
theorem normFromGalois_splitting_independent {J' : Type*} [Fintype J']
    (b : Module.Basis J K A) (b' : Module.Basis J' K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (f : F ⊗[K] A ≃ₐ[F] Matrix I I F)
    (R : Type uR) [CommRing R] [Algebra K R] (x : R ⊗[K] A) :
    normFromGalois b' f R x = normFromGalois b e R x := by
  rw [normFromGalois_basis_independent b b' f, normFromGalois_apply,
    normFromGalois_apply, descendedPolynomial_splitting_independent e f]

end Comparison

end Langlands.ReducedNorm
