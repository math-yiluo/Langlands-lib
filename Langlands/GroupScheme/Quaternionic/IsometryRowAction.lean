import Langlands.GroupScheme.Quaternionic.QuadraticValueExt
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.FiniteAlgebraRightRegular

/-! # The actual division-algebra row action of quaternionic isometries -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FiniteAlgebraUnits

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  {d : ℕ} (b : Module.Basis (Fin d) K A)

/-- At the ground field the tensor-basis matrix is the original regular matrix. -/
theorem rightMulMatrix_self (z : K ⊗[K] A) :
    rightMulMatrix b K z =
      LinearMap.toMatrix b b (LinearMap.mulRight K (Algebra.TensorProduct.lid K A z)) := by
  have he : z = (1 : K) ⊗ₜ[K] Algebra.TensorProduct.lid K A z := by
    apply (Algebra.TensorProduct.lid K A).injective
    simp
  calc
    rightMulMatrix b K z =
      rightMulMatrix b K ((1 : K) ⊗ₜ[K] Algebra.TensorProduct.lid K A z) := congrArg _ he
    _ = _ := by
      ext i j
      simp [rightMulMatrix, LinearMap.toMatrix_apply,
        Algebra.TensorProduct.tmul_mul_tmul]

/-- The ground-field regular matrix acts by actual inverse right multiplication. -/
theorem rightRegularHom_affine_action
    (a : GroupScheme.affinePoints (groupScheme b) (CommAlgCat.of K K)) (z : A) :
    ((rightRegularHom b).affineMatrix (CommAlgCat.of K K) a : Matrix (Fin d) (Fin d) K) *ᵥ
        b.equivFun z =
      b.equivFun (z * Algebra.TensorProduct.lid K A
        ((affinePointsEquiv b (CommAlgCat.of K K) a)⁻¹ : (K ⊗[K] A)ˣ)) := by
  rw [rightRegularHom_affineMatrix]
  change rightMulMatrix b K
    ((affinePointsEquiv b (CommAlgCat.of K K) a)⁻¹ : (K ⊗[K] A)ˣ) *ᵥ b.repr z = _
  rw [rightMulMatrix_self, LinearMap.toMatrix_mulVec_repr]
  rfl

end FiniteAlgebraUnits

namespace Quaternionic.IsometryCut

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]

/-- The tensor-unit comparison commutes with an involution extended from the ground field. -/
theorem lid_baseChange (τ : FirstKindInvolution K A) (z : K ⊗[K] A) :
    Algebra.TensorProduct.lid K A (τ.baseChange K z) =
      τ (Algebra.TensorProduct.lid K A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c a => simp
  | add z z' hz hz' => simp only [_root_.map_add, hz, hz']

/-- Ground-field scalar extension of a subspace is carried back to that subspace. -/
theorem lid_mem_of_mem_baseChange (M : Submodule K A) {z : K ⊗[K] A}
    (hz : z ∈ M.baseChange K) : Algebra.TensorProduct.lid K A z ∈ M := by
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul c a => simpa using M.smul_mem c a.2
  | add w w' hw hw' => simpa only [_root_.map_add] using M.add_mem hw hw'

/-- Actual defining defects commute with the ground-field tensor-unit comparison. -/
theorem lid_defect (τ : FirstKindInvolution K A) (Q : A) (z : K ⊗[K] A) :
    Algebra.TensorProduct.lid K A (defect τ Q z) =
      Algebra.TensorProduct.lid K A z * Q * τ (Algebra.TensorProduct.lid K A z) - Q := by
  simp only [defect, _root_.map_sub, _root_.map_mul, lid_baseChange,
    Algebra.TensorProduct.lid_tmul, one_smul]

end Quaternionic.IsometryCut

namespace Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]

/-- The actual tensor-algebra unit attached to a ground-field coefficient isometry point. -/
def isometryAffineUnits (q : σ.QuadraticForms n) :
    GroupScheme.affinePoints (σ.isometryGroup q) (CommAlgCat.of K K) →*
      (K ⊗[K] Matrix n n D)ˣ :=
  (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D))
    (CommAlgCat.of K K)).toMonoidHom.comp
    ((σ.isometryGroup q).affinePointsTarget (σ.isometryGroupι q) (CommAlgCat.of K K))

/-- The actual matrix unit attached to a ground-field coefficient isometry point. -/
def isometryMatrixPoint (q : σ.QuadraticForms n) :
    GroupScheme.affinePoints (σ.isometryGroup q) (CommAlgCat.of K K) →* (Matrix n n D)ˣ :=
  (Units.map (Algebra.TensorProduct.lid K (Matrix n n D)).toMonoidHom).comp (σ.isometryAffineUnits q)

/-- Every actual affine isometry point satisfies its tensor-algebra defining equations. -/
theorem isometryAffineUnits_defect_mem (q : σ.QuadraticForms n)
    (a : GroupScheme.affinePoints (σ.isometryGroup q) (CommAlgCat.of K K)) :
    IsometryCut.defect (σ.matrix n) (Quotient.out q) (σ.isometryAffineUnits q a : K ⊗[K] Matrix n n D)
      ∈ (σ.quadraticKernel n).baseChange K := by
  let hI := IsometryCut.isCutOutBy
    (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix n)) (Quotient.out q)
  have he : σ.isometryAffineUnits q a =
      ((Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy hI)
        (CommAlgCat.of K K) a).val) := by
    change Corepresented.affinePointsEquiv _
      (FiniteAlgebraUnits.corepresentableBy (Module.finBasis K (Matrix n n D)))
      (CommAlgCat.of K K) (a ≫ (Corepresented.cutHom hI).hom.hom) = _
    rw [Corepresented.cutHom]
    erw [Corepresented.groupSchemeMap_affinePoints]
    rfl
  rw [he]
  exact (Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy hI)
    (CommAlgCat.of K K) a).2

/-- The original matrix representative has alternating defect at every actual matrix point. -/
theorem isometryMatrixPoint_defect_mem (q : σ.QuadraticForms n)
    (a : GroupScheme.affinePoints (σ.isometryGroup q) (CommAlgCat.of K K)) :
    (σ.isometryMatrixPoint q a : Matrix n n D) * Quotient.out q *
        σ.matrix n (σ.isometryMatrixPoint q a : Matrix n n D) - Quotient.out q ∈
      σ.quadraticKernel n := by
  have he := IsometryCut.lid_mem_of_mem_baseChange (σ.quadraticKernel n)
    (σ.isometryAffineUnits_defect_mem q a)
  rw [IsometryCut.lid_defect] at he
  exact he

/-- Actual isometry matrix points fix the full quotient-valued form. -/
theorem quadraticPullback_isometryMatrixPoint (q : σ.QuadraticForms n)
    (a : GroupScheme.affinePoints (σ.isometryGroup q) (CommAlgCat.of K K)) :
    σ.quadraticPullback (σ.isometryMatrixPoint q a : Matrix n n D) q = q := by
  have he := (Submodule.Quotient.eq (σ.quadraticKernel n)).mpr
    (σ.isometryMatrixPoint_defect_mem q a)
  rw [← rectangularAdjoint_square, ← quadraticPullback_mk, Submodule.Quotient.mk_out] at he
  exact he

/-- The division-algebra row action is inverse right multiplication by the actual matrix point. -/
def isometryRowAction (q : σ.QuadraticForms n)
    (a : GroupScheme.affinePoints (σ.isometryGroup q) (CommAlgCat.of K K)) :
    Module.End D (n → D) :=
  (σ.isometryMatrixPoint q a⁻¹ : Matrix n n D).toLinearMapRight'

/-- Every row operator in the actual ground-field isometry action preserves the quadratic value. -/
theorem quadraticValue_isometryRowAction (q : σ.QuadraticForms n)
    (a : GroupScheme.affinePoints (σ.isometryGroup q) (CommAlgCat.of K K)) (z : n → D) :
    σ.quadraticValue (σ.isometryRowAction q a z) q = σ.quadraticValue z q :=
  (σ.quadraticPullback_eq_iff _ q).mp (σ.quadraticPullback_isometryMatrixPoint q a⁻¹) z

end Quaternionic.FirstKindInvolution

end Langlands.GroupScheme
