import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Mathlib.LinearAlgebra.SymplecticGroup

/-! # The standard symplectic group scheme over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Symplectic

variable (K : Type u) [Field K]

/-- The identity involution on the coefficient field. -/
def scalarInvolution : Quaternionic.FirstKindInvolution K K where
  toLinearMap := LinearMap.id
  map_one' := rfl
  map_mul' := mul_comm
  involutive' := fun _ => rfl

@[simp] theorem scalarInvolution_apply (x : K) : scalarInvolution K x = x := rfl

@[simp] theorem scalarInvolution_matrix {s : Type} [Fintype s] [DecidableEq s]
    (M : Matrix s s K) : (scalarInvolution K).matrix s M = M.transpose := rfl

/-- The standard alternating Gram matrix is trace-valued antihermitian, also in
characteristic two. -/
theorem isAntihermitian_J (n : ℕ) :
    (scalarInvolution K).IsAntihermitian (Matrix.J (Fin n) K) := by
  refine ⟨Matrix.J_transpose _ _, ?_⟩
  intro i
  have hi : Matrix.J (Fin n) K i i = 0 := by
    cases i <;> rfl
  rw [hi]
  exact Submodule.zero_mem _

/-- The standard alternating Gram matrix is nondegenerate. -/
theorem isUnit_J (n : ℕ) : IsUnit (Matrix.J (Fin n) K) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_J _ _)

/-- The standard symplectic group scheme `Sp_{2n}`: the closed isometry group of
the standard alternating form. -/
abbrev groupScheme (n : ℕ) : GroupScheme (Spec (CommRingCat.of K)) :=
  (scalarInvolution K).unitaryGroup (Matrix.J (Fin n) K)

/-- Its inclusion into the unit group scheme of the full matrix algebra. -/
def inclusion (n : ℕ) :
    groupScheme K n ⟶
      FiniteAlgebraUnits.groupScheme
        (Module.finBasis K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) :=
  (scalarInvolution K).unitaryGroupι (Matrix.J (Fin n) K)

theorem isClosedSubgroup_inclusion (n : ℕ) : IsClosedSubgroup (inclusion K n) :=
  (scalarInvolution K).isClosedSubgroup_unitaryGroupι _

instance isAffineHom_groupScheme (n : ℕ) : IsAffineHom (groupScheme K n).X.hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

variable {s : Type} [Fintype s] [DecidableEq s]

/-- The canonical scalar-extension isomorphism for a full matrix algebra. -/
def coefficientEquiv (R : Type u) [CommRing R] [Algebra K R] :
    R ⊗[K] Matrix s s K ≃ₐ[K] Matrix s s R :=
  (FiniteAlgebraUnits.MatrixPoints.coefficientEquiv K K R).trans
    (Algebra.TensorProduct.rid K K R).mapMatrix

theorem coefficientEquiv_tmul (R : Type u) [CommRing R] [Algebra K R]
    (r : R) (M : Matrix s s K) (i j : s) :
    coefficientEquiv K R (r ⊗ₜ[K] M) i j = r * algebraMap K R (M i j) := by
  simp [coefficientEquiv, FiniteAlgebraUnits.MatrixPoints.coefficientEquiv_tmul,
    Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]

theorem coefficientEquiv_one_tmul (R : Type u) [CommRing R] [Algebra K R]
    (M : Matrix s s K) :
    coefficientEquiv K R (1 ⊗ₜ[K] M) = M.map (algebraMap K R) := by
  ext i j
  simp [coefficientEquiv_tmul]

theorem coefficientEquiv_involution (R : Type u) [CommRing R] [Algebra K R]
    (x : R ⊗[K] Matrix s s K) :
    coefficientEquiv K R (((scalarInvolution K).matrix s).baseChange R x) =
      (coefficientEquiv K R x).transpose := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    ext i j
    simp [coefficientEquiv_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Matrix.transpose_add]

theorem coefficientEquiv_J (R : Type u) [CommRing R] [Algebra K R] (n : ℕ) :
    coefficientEquiv K R (1 ⊗ₜ[K] Matrix.J (Fin n) K) = Matrix.J (Fin n) R := by
  rw [coefficientEquiv_one_tmul, Matrix.map_J]

/-- Every matrix-unit-group point is an invertible matrix over the global sections
of its test scheme. -/
def ambientPointsEquiv (n : ℕ) (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))).X) ≃*
        Matrix.GeneralLinearGroup (Fin n ⊕ Fin n)
          ((algΓ (CommRingCat.of K)).obj T).unop :=
  (FiniteAlgebraUnits.pointsEquiv _ T).trans
    (Units.mapEquiv
      (coefficientEquiv (s := Fin n ⊕ Fin n)
        K ((algΓ (CommRingCat.of K)).obj T).unop).toMulEquiv)

/-- On every test scheme, membership in the represented subgroup is exactly the
standard symplectic matrix equation. -/
theorem mem_range_inclusion_iff (n : ℕ) {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))).X) :
    x ∈ (SubgroupFunctor.range (inclusion K n)).carrier T ↔
      (ambientPointsEquiv K n T x :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          ((algΓ (CommRingCat.of K)).obj T).unop) ∈
        Matrix.symplecticGroup (Fin n) ((algΓ (CommRingCat.of K)).obj T).unop := by
  rw [inclusion, Quaternionic.FirstKindInvolution.mem_range_unitaryGroupι_iff,
    ← (coefficientEquiv (s := Fin n ⊕ Fin n)
      K ((algΓ (CommRingCat.of K)).obj T).unop).injective.eq_iff]
  simp only [map_mul, coefficientEquiv_J, coefficientEquiv_involution]
  rfl

end Langlands.GroupScheme.Symplectic
