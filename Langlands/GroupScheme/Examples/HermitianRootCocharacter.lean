import Langlands.GroupScheme.Examples.HermitianRootRationalPoints
import Langlands.GroupScheme.Examples.SU3Cocharacter

/-! # The split diagonal cocharacter of the weighted Hermitian scheme -/

noncomputable section

universe u v z

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot

section Coefficients

variable {A : Type u} {B : Type v} {Middle : Type z}
  [CommRing A] [CommRing B] [Fintype Middle] [DecidableEq Middle]

/-- Coefficient maps preserve the actual hyperbolic diagonal matrices. -/
theorem map_diagonalEmbedding (f : A →+* B) (r : Aˣ) :
    Matrix.GeneralLinearGroup.map f
      (diagonalEmbedding r : Matrix.GeneralLinearGroup (Index Middle) A) =
      diagonalEmbedding (Units.map f.toMonoidHom r) := by
  apply Units.ext
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [diagonalMatrix, diagonalWeight, Matrix.diagonal_apply, Units.coe_map]

end Coefficients

namespace SchemeModel

open SU3Root
open SU3Root.SchemeModel (scalarUnit sectionToTensor_bar scalarUnit_naturality)

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- Ground scalar units give actual weighted special-unitary test points. -/
def cocharacterPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Gm (Spec (CommRingCat.of k))).X) →*
      (T ⟶ (groupScheme k L H w hw).X) where
  toFun x := (pointsEquiv k L H w hw T).symm
    ⟨diagonalEmbedding (scalarUnit k L T x),
      diagonalEmbedding_mem_specialUnitarySubgroup (tensorForm k L H T)
        (scalarUnit k L T x) (sectionToTensor_bar k L T _)⟩
  map_one' := by
    apply (pointsEquiv k L H w hw T).injective
    rw [MulEquiv.apply_symm_apply, (pointsEquiv k L H w hw T).map_one]
    apply Subtype.ext
    change diagonalEmbedding (scalarUnit k L T 1) = 1
    rw [map_one, map_one]
  map_mul' x y := by
    apply (pointsEquiv k L H w hw T).injective
    rw [MulEquiv.apply_symm_apply, (pointsEquiv k L H w hw T).map_mul,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change diagonalEmbedding (scalarUnit k L T (x * y)) =
      diagonalEmbedding (scalarUnit k L T x) * diagonalEmbedding (scalarUnit k L T y)
    rw [map_mul, map_mul]

@[simp] theorem pointsEquiv_cocharacterPoints (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    (pointsEquiv k L H w hw T (cocharacterPoints k L H w hw T x)).1 =
      diagonalEmbedding (scalarUnit k L T x) :=
  congrArg Subtype.val ((pointsEquiv k L H w hw T).apply_symm_apply _)

/-- The prescribed diagonal points commute with every actual test restriction. -/
theorem cocharacterPoints_naturality {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    cocharacterPoints k L H w hw T' (a ≫ x) =
      a ≫ cocharacterPoints k L H w hw T x := by
  apply (pointsEquiv k L H w hw T').injective
  rw [pointsEquiv_map]
  apply Subtype.ext
  change _ = Matrix.GeneralLinearGroup.map
    (SpecialLinear.WeilRoot.tensorMap k L a)
      (pointsEquiv k L H w hw T (cocharacterPoints k L H w hw T x)).1
  rw [pointsEquiv_cocharacterPoints, pointsEquiv_cocharacterPoints,
    map_diagonalEmbedding, scalarUnit_naturality]

/-- The actual split diagonal cocharacter of the weighted Hermitian group scheme. -/
def cocharacter :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme k L H w hw :=
  homOfPoints (cocharacterPoints k L H w hw) (cocharacterPoints_naturality k L H w hw)

/-- The cocharacter has the prescribed actual general-linear matrix on every test. -/
theorem pointsEquiv_cocharacter {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    (pointsEquiv k L H w hw T (x ≫ (cocharacter k L H w hw).hom.hom)).1 =
      diagonalEmbedding (scalarUnit k L T x) := by
  rw [cocharacter, comp_homOfPoints, pointsEquiv_cocharacterPoints]

/-- The explicit all-test matrix is diagonal with entries t, identity, and t inverse. -/
theorem pointsEquiv_cocharacter_val {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    ((pointsEquiv k L H w hw T (x ≫ (cocharacter k L H w hw).hom.hom)).1 :
      Matrix (Index Middle) (Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
        diagonalMatrix (scalarUnit k L T x) := by
  rw [pointsEquiv_cocharacter, diagonalEmbedding_val]

/-- The same matrix is the actual tensor matrix of the ambient inclusion. -/
theorem tensorMatrixEquiv_cocharacter {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    (SpecialLinear.WeilRoot.tensorMatrixEquiv k L T
      (x ≫ (cocharacter k L H w hw).hom.hom ≫ (inclusion k L H w hw).hom.hom) :
        Matrix (Index Middle) (Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
          diagonalMatrix (scalarUnit k L T x) := by
  rw [← Category.assoc, ← pointsEquiv_val]
  exact pointsEquiv_cocharacter_val k L H w hw x

end SchemeModel
end Langlands.GroupScheme.HermitianRoot
