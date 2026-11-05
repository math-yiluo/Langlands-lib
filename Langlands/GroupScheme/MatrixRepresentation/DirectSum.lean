import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Multiplicative
import Mathlib.Data.Matrix.Block

/-! # Finite direct sums of actual matrix representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {I : Type} [Fintype I] [DecidableEq I] {n : I → Type}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  (ρ : ∀ i, MatrixRepresentation G (n i))

/-- The block diagonal point matrices of a finite family form a monoid action. -/
def directSumMatrixHom (T : Over (Spec R)) :
    (T ⟶ G.X) →* Matrix (Σ i, n i) (Σ i, n i) Γ(T.left, ⊤) where
  toFun x := Matrix.blockDiagonal' fun i =>
    ((ρ i).pointMatrix T x : Matrix (n i) (n i) Γ(T.left, ⊤))
  map_one' := by
    simp only [map_one, Matrix.GeneralLinearGroup.coe_one]
    exact Matrix.blockDiagonal'_one
  map_mul' x y := by
    simp only [map_mul, Matrix.GeneralLinearGroup.coe_mul]
    exact Matrix.blockDiagonal'_mul _ _

/-- Block diagonal point matrices commute with pullback on scheme tests. -/
theorem directSumMatrixHom_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    directSumMatrixHom ρ T' (a ≫ x) =
      (directSumMatrixHom ρ T x).map a.left.appTop.hom := by
  change Matrix.blockDiagonal' (fun i =>
    ((ρ i).pointMatrix T' (a ≫ x) : Matrix (n i) (n i) Γ(T'.left, ⊤))) =
      (Matrix.blockDiagonal' fun i =>
        ((ρ i).pointMatrix T x : Matrix (n i) (n i) Γ(T.left, ⊤))).map a.left.appTop.hom
  rw [Matrix.blockDiagonal'_map _ _ (map_zero _)]
  congr 1

/-- The natural general-linear point family of the direct sum. -/
def directSumPoints (T : Over (Spec R)) :
    (T ⟶ G.X) →* (T ⟶ (GeneralLinear.groupScheme (Σ i, n i) R).X) :=
  (GeneralLinear.pointsEquiv (Σ i, n i) R T).symm.toMonoidHom.comp
    (directSumMatrixHom ρ T).toHomUnits

/-- The direct-sum point family is natural on all relative schemes. -/
theorem directSumPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    directSumPoints ρ T' (a ≫ x) = a ≫ directSumPoints ρ T x := by
  apply (GeneralLinear.pointsEquiv (Σ i, n i) R T').injective
  rw [GeneralLinear.pointsEquiv_naturality]
  simp only [directSumPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change (directSumMatrixHom ρ T').toHomUnits (a ≫ x) =
    Matrix.GeneralLinearGroup.map a.left.appTop.hom
      ((directSumMatrixHom ρ T).toHomUnits x)
  apply Units.ext
  exact directSumMatrixHom_naturality ρ a x

/-- The finite direct sum as an actual group-scheme representation. -/
def directSum : MatrixRepresentation G (Σ i, n i) :=
  homOfPoints (directSumPoints ρ) (directSumPoints_naturality ρ)

/-- The direct-sum representation has exactly the prescribed block matrices. -/
theorem directSum_pointMatrix (T : Over (Spec R)) (x : T ⟶ G.X) :
    (directSum ρ).pointMatrix T x =
      (directSumMatrixHom ρ T).toHomUnits x := by
  rw [pointMatrix_apply, directSum, comp_homOfPoints]
  exact (GeneralLinear.pointsEquiv (Σ i, n i) R T).apply_symm_apply _

/-- The underlying matrix on every test is the block diagonal matrix. -/
theorem directSum_pointMatrix_val (T : Over (Spec R)) (x : T ⟶ G.X) :
    ((directSum ρ).pointMatrix T x :
      Matrix (Σ i, n i) (Σ i, n i) Γ(T.left, ⊤)) =
        Matrix.blockDiagonal' fun i =>
          ((ρ i).pointMatrix T x : Matrix (n i) (n i) Γ(T.left, ⊤)) := by
  rw [directSum_pointMatrix]
  rfl

/-- The full all-test kernel of the direct sum is the common kernel of its
factors, including for empty families and empty factor dimensions. -/
theorem directSum_pointMatrix_eq_one_iff (T : Over (Spec R)) (x : T ⟶ G.X) :
    (directSum ρ).pointMatrix T x = 1 ↔ ∀ i, (ρ i).pointMatrix T x = 1 := by
  constructor
  · intro h i
    have hv := congrArg Units.val h
    rw [directSum_pointMatrix_val] at hv
    have hh := Matrix.blockDiagonal'_injective
      (hv.trans (Matrix.blockDiagonal'_one).symm)
    apply Units.ext
    exact congrFun hh i
  · intro h
    apply Units.ext
    rw [directSum_pointMatrix_val]
    simp only [h, Matrix.GeneralLinearGroup.coe_one]
    exact Matrix.blockDiagonal'_one

/-- Direct sum commutes with the actual base-ring rational matrices. -/
theorem directSum_rationalMatrix_val
    (x : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    ((directSum ρ).rationalMatrix x : Matrix (Σ i, n i) (Σ i, n i) R) =
      Matrix.blockDiagonal' fun i => ((ρ i).rationalMatrix x : Matrix (n i) (n i) R) := by
  change ((directSum ρ).pointMatrix (Over.mk (𝟙 (Spec R))) x :
    Matrix (Σ i, n i) (Σ i, n i) Γ((Over.mk (𝟙 (Spec R))).left, ⊤)).map
      (Scheme.ΓSpecIso R).hom.hom = _
  rw [directSum_pointMatrix_val, Matrix.blockDiagonal'_map _ _ (map_zero _)]
  rfl

end Langlands.GroupScheme.MatrixRepresentation
