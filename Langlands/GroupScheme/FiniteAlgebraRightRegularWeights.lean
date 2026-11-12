import Langlands.GroupScheme.FiniteAlgebraRightRegularAffine
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusWeightPair

/-! # Split-torus weight elements in the original finite algebra -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  {d : ℕ} (b : Module.Basis (Fin d) k A)

/-- The actual unit in the original algebra represented by an affine
base-field point of its unit group. -/
def baseAffineUnit :
    ((algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) k)) ⟶ (groupScheme b).X) →* Aˣ :=
  (Units.mapEquiv (Algebra.TensorProduct.lid k A).toMulEquiv).toMonoidHom.comp
    (affinePointsEquiv b (CommAlgCat.of (CommRingCat.of k) k)).toMonoidHom

variable (I : Type u) [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ groupScheme b)

/-- The original algebra element with the coordinates of a universal
weight column in the inverse-right-regular representation. -/
def torusCoefficientElement (m : I → ℤ) (j : Fin d) : A :=
  b.equivFun.symm
    (GeneralLinear.CocharacterDiagonal.coefficientColumn I
      ((rightRegularRepresentation b).restrict i) m j)

@[simp] theorem equivFun_torusCoefficientElement (m : I → ℤ) (j : Fin d) :
    b.equivFun (torusCoefficientElement b I i m j) =
      GeneralLinear.CocharacterDiagonal.coefficientColumn I
        ((rightRegularRepresentation b).restrict i) m j :=
  b.equivFun.apply_symm_apply _

theorem torusCoefficientElement_ne_zero {m : I → ℤ} {j : Fin d}
    (h : GeneralLinear.CocharacterDiagonal.coefficientColumn I
      ((rightRegularRepresentation b).restrict i) m j ≠ 0) :
    torusCoefficientElement b I i m j ≠ 0 := by
  intro hz
  apply h
  rw [← equivFun_torusCoefficientElement, hz, map_zero]

/-- The universal coefficient element is an eigenvector for right
multiplication by the inverse of every actual base-field torus point. -/
theorem torusCoefficientElement_eigen (m : I → ℤ) (j : Fin d) (t : I → kˣ) :
    torusCoefficientElement b I i m j *
        (baseAffineUnit b
          ((splitTorus.algebraPointsEquiv I k).symm t ≫ i.hom.hom))⁻¹ =
      (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : k) •
        torusCoefficientElement b I i m j := by
  let R := CommAlgCat.of (CommRingCat.of k) k
  let x := (splitTorus.algebraPointsEquiv I k).symm t ≫ i.hom.hom
  let y := torusCoefficientElement b I i m j
  let v := GeneralLinear.CocharacterDiagonal.coefficientColumn I
    ((rightRegularRepresentation b).restrict i) m j
  have hy : ((b.baseChange k).repr (1 ⊗ₜ[k] y) : Fin d → k) = v := by
    calc
      _ = b.equivFun y := by ext a; simp
      _ = v := equivFun_torusCoefficientElement b I i m j
  have hv := GeneralLinear.CocharacterDiagonal.coefficientColumn_weight I
    ((rightRegularRepresentation b).restrict i) t m j
  change
    (((rightRegularRepresentation b).restrict i).affineMatrix R
      ((splitTorus.algebraPointsEquiv I k).symm t) : Matrix (Fin d) (Fin d) k) *ᵥ v =
      (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : k) • v at hv
  rw [MatrixRepresentation.affineMatrix_restrict,
    affineMatrix_rightRegularRepresentation] at hv
  change rightMulMatrix b k ((affinePointsEquiv b R x)⁻¹).val *ᵥ v =
    (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : k) • v at hv
  have hy' : (b.baseChange k).equivFun ((1 : k) ⊗ₜ[k] y) = v := hy
  have he : ((1 : k) ⊗ₜ[k] y) * ((affinePointsEquiv b R x)⁻¹).val =
      (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : k) •
        ((1 : k) ⊗ₜ[k] y) := by
    apply (b.baseChange k).equivFun.injective
    change ((b.baseChange k).repr
      (((1 : k) ⊗ₜ[k] y) * ((affinePointsEquiv b R x)⁻¹).val) :
        Fin d → k) = _
    rw [← rightMulMatrix_mulVec_repr]
    simpa only [map_smul, hy, hy'] using hv
  have h := congrArg (Algebra.TensorProduct.lid k A) he
  change y * (Algebra.TensorProduct.lid k A) ((affinePointsEquiv b R x)⁻¹).val =
    (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : k) • y
  simpa only [map_mul, map_smul, Algebra.TensorProduct.lid_tmul, one_smul] using h

end Langlands.GroupScheme.FiniteAlgebraUnits
