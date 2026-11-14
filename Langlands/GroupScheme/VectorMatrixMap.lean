import Langlands.GroupScheme.VectorDiagonalKernel
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Matrix homomorphisms of polynomial vector groups -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.VectorGroup

variable {R : CommRingCat.{u}} {n m p : ℕ}

/-- Matrix multiplication on vector coordinates on every scheme test. -/
def matrixPoints (M : Matrix (Fin m) (Fin n) R) (T : Over (Spec R)) :
    (T ⟶ (groupScheme R n).X) →* (T ⟶ (groupScheme R m).X) where
  toFun x := (coordinates R m T).symm
    (Multiplicative.ofAdd (M.map (scalarMap T) *ᵥ (coordinates R n T x).toAdd))
  map_one' := by
    apply (coordinates R m T).injective
    apply Multiplicative.toAdd.injective
    simp only [MulEquiv.apply_symm_apply, map_one]
    change M.map (scalarMap T) *ᵥ 0 = 0
    exact Matrix.mulVec_zero _
  map_mul' x y := by
    apply (coordinates R m T).injective
    apply Multiplicative.toAdd.injective
    simp only [MulEquiv.apply_symm_apply, map_mul]
    change M.map (scalarMap T) *ᵥ
        ((coordinates R n T x).toAdd + (coordinates R n T y).toAdd) =
      M.map (scalarMap T) *ᵥ (coordinates R n T x).toAdd +
        M.map (scalarMap T) *ᵥ (coordinates R n T y).toAdd
    exact Matrix.mulVec_add _ _ _

@[simp]
theorem matrixPoints_coord (M : Matrix (Fin m) (Fin n) R) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R n).X) :
    (coordinates R m T (matrixPoints M T x)).toAdd =
      M.map (scalarMap T) *ᵥ (coordinates R n T x).toAdd :=
  congrArg Multiplicative.toAdd ((coordinates R m T).apply_symm_apply _)

theorem matrixPoints_natural (M : Matrix (Fin m) (Fin n) R)
    {T W : Over (Spec R)} (f : W ⟶ T) (x : T ⟶ (groupScheme R n).X) :
    matrixPoints M W (f ≫ x) = f ≫ matrixPoints M T x := by
  apply points_ext
  intro j
  rw [matrixPoints_coord, coordinates_comp, coordinates_comp]
  dsimp only
  rw [matrixPoints_coord, RingHom.map_mulVec]
  congr 1
  ext i l
  exact (congrArg (fun g : R →+* Γ(W.left, ⊤) => g (M i l))
    (coefficientMap_comp f)).symm

/-- The group-scheme homomorphism with the given coefficient matrix. -/
def matrixHom (M : Matrix (Fin m) (Fin n) R) :
    groupScheme R n ⟶ groupScheme R m :=
  homOfPoints (matrixPoints M) (matrixPoints_natural M)

@[simp]
theorem coordinates_matrixHom (M : Matrix (Fin m) (Fin n) R) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R n).X) :
    (coordinates R m T (x ≫ (matrixHom M).hom.hom)).toAdd =
      M.map (scalarMap T) *ᵥ (coordinates R n T x).toAdd := by
  rw [matrixHom, comp_homOfPoints, matrixPoints_coord]

@[simp]
theorem matrixHom_one : matrixHom (R := R) (1 : Matrix (Fin n) (Fin n) R) = 𝟙 _ := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  rw [coordinates_matrixHom, Grp.id_hom_hom, Category.comp_id]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

/-- Matrix composition has the usual order on column coordinates. -/
theorem matrixHom_comp (M : Matrix (Fin m) (Fin n) R)
    (N : Matrix (Fin p) (Fin m) R) :
    matrixHom M ≫ matrixHom N = matrixHom (N * M) := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  rw [Grp.comp_hom_hom, ← Category.assoc, coordinates_matrixHom,
    coordinates_matrixHom, coordinates_matrixHom, Matrix.map_mul,
    Matrix.mulVec_mulVec]

theorem matrixHom_diagonal (c : Fin n → R) :
    matrixHom (Matrix.diagonal c) = diagonal c := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  rw [coordinates_matrixHom, coordinates_diagonal]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, apply_ite]

/-- An invertible coefficient matrix gives an actual group-scheme isomorphism. -/
def matrixIso (M : (Matrix (Fin n) (Fin n) R)ˣ) :
    groupScheme R n ≅ groupScheme R n where
  hom := matrixHom (M : Matrix (Fin n) (Fin n) R)
  inv := matrixHom ((M⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)
  hom_inv_id := by rw [matrixHom_comp, Units.inv_mul, matrixHom_one]
  inv_hom_id := by rw [matrixHom_comp, Units.mul_inv, matrixHom_one]

section BaseChange

variable {A : CommRingCat.{u}} (ρ : R ⟶ A)

/-- Matrix maps commute with actual base change, with every coefficient mapped. -/
theorem matrixHom_baseChange (M : Matrix (Fin m) (Fin n) R) :
    (baseChangeIso (n := n) ρ).hom ≫ matrixHom (M.map ρ.hom) =
      (GroupScheme.baseChange (Spec.map ρ)).map (matrixHom M) ≫
        (baseChangeIso (n := m) ρ).hom := by
  apply hom_ext_points
  intro T x
  apply points_ext
  intro j
  simp only [Grp.comp_hom_hom, ← Category.assoc, coordinates_matrixHom,
    coordinates_baseChangeIso_hom]
  change ((M.map ρ.hom).map (scalarMap T) *ᵥ
      (baseChangeCoordinates ρ T x).toAdd) j =
    (coordinates R m ((Over.map (Spec.map ρ)).obj T)
      (baseChangePointsEquiv (Spec.map ρ) (groupScheme R m) T
        (x ≫ ((GroupScheme.baseChange (Spec.map ρ)).map (matrixHom M)).hom.hom))).toAdd j
  rw [baseChangePointsEquiv_comp, coordinates_matrixHom, coefficientMap_map]
  rfl

end BaseChange

end Langlands.GroupScheme.VectorGroup
