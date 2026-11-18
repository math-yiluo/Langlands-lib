import Langlands.GroupScheme.OrthogonalMatrix.Comparison
import Langlands.GroupScheme.Quaternionic.NormOneIsometry
import Langlands.GroupScheme.Quaternionic.ScalarInvolution
import Langlands.GroupScheme.OrthogonalMatrix.Basic
import Langlands.Algebra.ReducedNormFiniteChart
import Mathlib.RingTheory.MatrixAlgebra

/-! # Ordinary matrix coordinates for scalar norm-one isometry points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.Quaternionic.ScalarMatrixCoordinates

open FirstKindInvolution

variable (K : Type u) [Field K] {n : Type} [Fintype n] [DecidableEq n]
  (R : Type u) [CommRing R] [Algebra K R]

/-- The scalar tensor matrix chart, over every coefficient algebra. -/
def matrixEquiv : R ⊗[K] Matrix n n K ≃ₐ[K] Matrix n n R :=
  OrthogonalMatrix.chart K n R

@[simp] theorem matrixEquiv_tmul (r : R) (M : Matrix n n K) :
    matrixEquiv K R (r ⊗ₜ[K] M) = r • M.map (algebraMap K R) :=
  by apply OrthogonalMatrix.chart_tmul

variable {R} in
/-- The scalar chart commutes with every coefficient-algebra homomorphism. -/
theorem matrixEquiv_naturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (z : R ⊗[K] Matrix n n K) :
    matrixEquiv K S (Algebra.TensorProduct.map f (AlgHom.id K (Matrix n n K)) z) =
      (matrixEquiv K R z).map f :=
  by apply OrthogonalMatrix.chart_naturality

/-- The chart carries the scalar matrix involution to ordinary transpose. -/
theorem matrixEquiv_baseChange (z : R ⊗[K] Matrix n n K) :
    matrixEquiv K R (((scalar K).matrix n).baseChange R z) =
      (matrixEquiv K R z).transpose :=
  by apply OrthogonalMatrix.chart_baseChange

/-- The base-changed quadratic kernel is exactly the ordinary alternating
matrix submodule in the scalar chart, including for nonreduced algebras. -/
theorem mem_quadraticKernel_baseChange_iff (z : R ⊗[K] Matrix n n K) :
    z ∈ ((scalar K).quadraticKernel n).baseChange R ↔
      OrthogonalMatrix.IsAlt (matrixEquiv K R z) :=
  by apply OrthogonalMatrix.mem_quadraticKernel_baseChange_iff

/-- The scalar chart intertwines the isometry defect with the ordinary matrix
quadratic defect. -/
theorem matrixEquiv_defect (Q : Matrix n n K) (z : R ⊗[K] Matrix n n K) :
    matrixEquiv K R (IsometryCut.defect ((scalar K).matrix n) Q z) =
      matrixEquiv K R z * Q.map (algebraMap K R) * (matrixEquiv K R z).transpose -
        Q.map (algebraMap K R) :=
  by apply OrthogonalMatrix.chart_defect

variable [Nonempty n]

/-- In the scalar tensor chart the canonical reduced norm is the determinant,
over every commutative coefficient algebra. -/
theorem reducedNorm_eq_det (z : R ⊗[K] Matrix n n K) :
    CentralSimple.reducedNorm K (Matrix n n K) R z = (matrixEquiv K R z).det := by
  rw [CentralSimple.reducedNorm_eq_det_fintype K (Matrix n n K)
    (Algebra.TensorProduct.lid K (Matrix n n K)) R]
  congr 1
  induction z using TensorProduct.inductionOn with
  | tmul r M =>
    rw [ReducedNorm.splittingMap_tmul, matrixEquiv_tmul]
    simp only [Algebra.TensorProduct.lid_tmul, one_smul]
  | add z w hz hw => rw [_root_.map_add, _root_.map_add, hz, hw]

/-- All-test-scheme matrix equations for the actual scalar norm-one group. -/
theorem mem_range_normOneIsometryAmbientι_iff (q : (scalar K).QuadraticForms n)
    (Q : Matrix n n K) (hQ : (Submodule.Quotient.mk Q : (scalar K).QuadraticForms n) = q)
    {T : Over (Spec (CommRingCat.of K))}
    (z : T ⟶ (CentralSimpleUnits.groupScheme K (Matrix n n K)).X) :
    z ∈ (SubgroupFunctor.range ((scalar K).normOneIsometryAmbientι q)).carrier T ↔
      let g := matrixEquiv K ((algΓ (CommRingCat.of K)).obj T).unop
        (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n K)) T z :
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n K)
      OrthogonalMatrix.IsAlt (g * Q.map (algebraMap K _) * g.transpose -
        Q.map (algebraMap K _)) ∧ g.det = 1 := by
  rw [FirstKindInvolution.mem_range_normOneIsometryAmbientι_iff_equations (scalar K) q Q hQ,
    mem_quadraticKernel_baseChange_iff, matrixEquiv_defect]
  refine and_congr_right fun _ => ?_
  rw [← Units.val_inj, CentralSimple.reducedNormUnits_val, Units.val_one, reducedNorm_eq_det]

end Langlands.GroupScheme.Quaternionic.ScalarMatrixCoordinates
