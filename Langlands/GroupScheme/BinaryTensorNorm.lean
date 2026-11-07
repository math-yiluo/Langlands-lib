import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Langlands.Algebra.BinaryReducedNorm

/-! # Binary reduced norm over every commutative test algebra -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits.BinaryNorm

open Langlands.BinaryElementary Langlands.ReducedNorm Langlands.CentralSimple

section Splitting

variable {k D L : Type u} [Field k] [Ring D] [Algebra k D]
  [Field L] [Algebra k L] {I : Type} [Fintype I] [DecidableEq I]
  (e : L ⊗[k] D ≃ₐ[L] Matrix I I L)

/-- The actual binary splitting map is the block map of the coefficient splitting map. -/
theorem splittingMap_binary (S : Type u) [CommRing S] [Algebra k S]
    [Algebra L S] [IsScalarTower k L S] (x : S ⊗[k] Matrix (Fin 2) (Fin 2) D) :
    splittingMap (Splitting.chart e) S x =
      Representation.blockMap (splittingMap e S).toRingHom (MatrixPoints.coefficientEquiv (m := Fin 2) k D S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s M =>
    rw [splittingMap_tmul, Splitting.chart_tmul, one_smul]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Representation.blockMap, MatrixPoints.coefficientEquiv_tmul,
        splittingMap_tmul, Splitting.coefficientRepresentation, Matrix.map_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Extend a tensor coefficient to a splitting-field algebra and represent it by matrices. -/
def tensorRepresentation (R : Type u) [CommRing R] [Algebra k R] :
    R ⊗[k] D →+* Matrix I I (L ⊗[k] R) :=
  (splittingMap e (L ⊗[k] R)).toRingHom.comp
    (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (A := L))
      (AlgHom.id k D)).toRingHom

end Splitting

variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
  [FiniteDimensional k D] [Algebra.IsCentral k D] [IsSimpleRing D]

/-- The canonical reduced norm transported to binary matrices over tensor coefficients. -/
def tensorNorm (R : Type u) [CommRing R] [Algebra k R] :
    GL₂ (R ⊗[k] D) →* Rˣ :=
  (reducedNormUnits k (Matrix (Fin 2) (Fin 2) D) R).comp
    (Units.mapEquiv (MatrixPoints.coefficientEquiv (m := Fin 2) k D R).symm.toMulEquiv).toMonoidHom

/-- A faithful splitting-field extension identifies the tensor norm with a block determinant. -/
theorem tensorNorm_baseChange {L : Type u} [Field L] [Algebra k L]
    {I : Type} [Fintype I] [DecidableEq I]
    (e : L ⊗[k] D ≃ₐ[L] Matrix I I L)
    (R : Type u) [CommRing R] [Algebra k R] (g : GL₂ (R ⊗[k] D)) :
    Units.map (Algebra.TensorProduct.includeRight (A := L) : R →ₐ[k] L ⊗[k] R).toMonoidHom
        (tensorNorm k D R g) = Representation.binaryNorm (tensorRepresentation e R) g := by
  apply Units.ext
  change Algebra.TensorProduct.includeRight
      (reducedNorm k (Matrix (Fin 2) (Fin 2) D) R
        ((MatrixPoints.coefficientEquiv (m := Fin 2) k D R).symm g.val)) = _
  rw [← reducedNorm_naturality k (Matrix (Fin 2) (Fin 2) D)
    (Algebra.TensorProduct.includeRight (A := L)),
    reducedNorm_eq_det_fintype k (Matrix (Fin 2) (Fin 2) D) (Splitting.chart e),
    splittingMap_binary e, MatrixPoints.coefficientEquiv_naturality,
    AlgEquiv.apply_symm_apply]
  rfl

/-- Every upper elementary tensor matrix has canonical reduced norm one. -/
theorem tensorNorm_upper (R : Type u) [CommRing R] [Algebra k R] (a : R ⊗[k] D) :
    tensorNorm k D R (upper a) = 1 := by
  apply Units.map_injective (Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective k (finiteGaloisSplittingField k D)))
  rw [tensorNorm_baseChange k D (finiteGaloisSplittingChart k D), map_one,
    Representation.binaryNorm_upper]

/-- Every lower elementary tensor matrix has canonical reduced norm one. -/
theorem tensorNorm_lower (R : Type u) [CommRing R] [Algebra k R] (a : R ⊗[k] D) :
    tensorNorm k D R (lower a) = 1 := by
  apply Units.map_injective (Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective k (finiteGaloisSplittingField k D)))
  rw [tensorNorm_baseChange k D (finiteGaloisSplittingChart k D), map_one,
    Representation.binaryNorm_lower]

/-- A diagonal unit paired with its inverse has canonical reduced norm one. -/
theorem tensorNorm_diagonal_inverse (R : Type u) [CommRing R] [Algebra k R]
    (a : (R ⊗[k] D)ˣ) : tensorNorm k D R (diagonal a a⁻¹) = 1 := by
  apply Units.map_injective (Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective k (finiteGaloisSplittingField k D)))
  rw [tensorNorm_baseChange k D (finiteGaloisSplittingChart k D), map_one,
    Representation.binaryNorm_diagonal, map_inv, mul_inv_cancel]

end Langlands.GroupScheme.FiniteAlgebraUnits.BinaryNorm
