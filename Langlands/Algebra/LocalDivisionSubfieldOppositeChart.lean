import Langlands.Algebra.LocalDivisionDegree
import Langlands.Algebra.CentralSimpleScalarExtension
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The right multiplication splitting chart of an embedded field -/

noncomputable section

namespace Langlands.CentralDivision

open Module Matrix
open scoped TensorProduct

universe u s

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

private def subfieldRightMultiplication :
    letI := localDivisionSubfieldLeftModule K D ι
    Dᵐᵒᵖ →+* Module.End L D := by
  letI := localDivisionSubfieldLeftModule K D ι
  refine
    { toFun := fun r =>
        { toFun := fun x => x * r.unop
          map_add' := fun x y => add_mul x y r.unop
          map_smul' := fun a x => by
            change (ι a * x) * r.unop = ι a * (x * r.unop)
            exact mul_assoc _ _ _ }
      map_zero' := LinearMap.ext fun x => mul_zero x
      map_one' := LinearMap.ext fun x => mul_one x
      map_add' := fun a b => LinearMap.ext fun x => mul_add x a.unop b.unop
      map_mul' := fun a b => LinearMap.ext fun x => (mul_assoc x b.unop a.unop).symm }

local notation "Index" => Fin (CentralSimple.reducedDegree K D)

variable (b : letI := localDivisionSubfieldLeftModule K D ι
              Basis (Fin (CentralSimple.reducedDegree K D)) L D)

private def subfieldOppositeMatrixRepresentation : Dᵐᵒᵖ →ₐ[K] Matrix Index Index L := by
  letI := localDivisionSubfieldLeftModule K D ι
  let m := LinearMap.toMatrixAlgEquiv b
  let r := subfieldRightMultiplication K D ι
  refine { m.toRingHom.comp r with commutes' := ?_ }
  intro a
  change m (r (algebraMap K Dᵐᵒᵖ a)) = algebraMap K (Matrix Index Index L) a
  have h : r (algebraMap K Dᵐᵒᵖ a) = algebraMap L (Module.End L D) (algebraMap K L a) := by
    ext x
    change x * algebraMap K D a = ι (algebraMap K L a) * x
    rw [ι.commutes, Algebra.commutes]
  rw [h, m.commutes]
  rfl

variable [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- In a basis for the left subfield action, right multiplication gives the
matrix splitting chart for the opposite division algebra. -/
def subfieldOppositeSplittingChart :
    L ⊗[K] Dᵐᵒᵖ ≃ₐ[L] Matrix Index Index L := by
  let f := AlgHom.liftEquiv K L Dᵐᵒᵖ (Matrix Index Index L)
    (subfieldOppositeMatrixRepresentation K D ι b)
  let : IsSimpleRing (L ⊗[K] Dᵐᵒᵖ) := CentralSimple.isSimpleRing_baseChange K Dᵐᵒᵖ L
  have hdim : Module.finrank L (L ⊗[K] Dᵐᵒᵖ) = Module.finrank L (Matrix Index Index L) := by
    have h := (MulOpposite.opLinearEquiv K : D ≃ₗ[K] Dᵐᵒᵖ).symm.finrank_eq
    rw [Module.finrank_baseChange, h, CentralSimple.finrank_eq_reducedDegree_mul_self,
      Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]
  exact AlgEquiv.ofBijective f ⟨f.toRingHom.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) hdim).mp
      f.toRingHom.injective⟩

/-- On a pure tensor the splitting chart acts by left coefficient
multiplication and right multiplication by the original division element. -/
theorem subfieldOppositeSplittingChart_tmul_mulVec (a : L) (r : Dᵐᵒᵖ) (x : D) :
    letI := localDivisionSubfieldLeftModule K D ι
    subfieldOppositeSplittingChart K D ι b (a ⊗ₜ[K] r) *ᵥ b.repr x =
      b.repr (ι a * x * r.unop) := by
  let := localDivisionSubfieldLeftModule K D ι
  let f := subfieldOppositeMatrixRepresentation K D ι b
  change (AlgHom.liftEquiv K L Dᵐᵒᵖ (Matrix Index Index L) f (a ⊗ₜ[K] r)) *ᵥ b.repr x = _
  rw [AlgHom.liftEquiv_tmul, Matrix.smul_mulVec]
  change a • (LinearMap.toMatrix b b ((subfieldRightMultiplication K D ι) r) *ᵥ b.repr x) = _
  rw [LinearMap.toMatrix_mulVec_repr]
  change a • (b.equivFun (x * r.unop)) = b.equivFun (ι a * x * r.unop)
  rw [← map_smul, mul_assoc]
  rfl

end Langlands.CentralDivision
