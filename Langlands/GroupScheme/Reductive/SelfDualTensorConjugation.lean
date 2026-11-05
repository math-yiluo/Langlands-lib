import Langlands.GroupScheme.Reductive.TensorConjugation
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation

/-! # Conjugation maps from actual self-dual tensor squares -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix Kronecker CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

section TensorIntertwiners

variable {n m r s : Type}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
  {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
  {τ : MatrixRepresentation G r} {π : MatrixRepresentation G s}

/-- The Kronecker matrix of actual intertwiners intertwines the actual tensor
representations. -/
theorem Intertwines.tensor {C : Matrix r n k} {D : Matrix s m k}
    (hC : Intertwines ρ τ C) (hD : Intertwines σ π D) :
    Intertwines (ρ.tensor σ) (τ.tensor π) (C ⊗ₖ D) := by
  intro A g
  have hmap : (C ⊗ₖ D).map (algebraMap k A) =
      C.map (algebraMap k A) ⊗ₖ D.map (algebraMap k A) := by
    ext i j
    exact map_mul (algebraMap k A) _ _
  rw [hmap, tensor_affineMatrix, tensor_affineMatrix,
    GeneralLinear.kroneckerHom_coe, GeneralLinear.kroneckerHom_coe,
    ← Matrix.mul_kronecker_mul, hC A g, hD A g, Matrix.mul_kronecker_mul]

end TensorIntertwiners

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Apply an invertible self-duality coordinate change in the second tensor
factor and the identity in the first. -/
def selfDualTensorCoordinates (D : GL m k) : GL (m × m) k :=
  GeneralLinear.kroneckerHom m m k (1, D)

/-- A supplied actual self-duality intertwiner induces the tensor-square to
tensor-dual intertwiner. -/
theorem intertwines_selfDualTensorCoordinates {σ : MatrixRepresentation G m}
    (D : GL m k) (hD : Intertwines σ σ.dual D.val) :
    Intertwines (σ.tensor σ) (σ.tensor σ.dual) (selfDualTensorCoordinates D).val := by
  have hid : Intertwines σ σ (1 : Matrix m m k) := by
    intro A g
    simp
  exact hid.tensor hD

/-- The self-duality coordinate change preserves nonzero tensor vectors. -/
theorem selfDualTensorCoordinates_mulVec_ne_zero_iff (D : GL m k) (x : m × m → k) :
    (selfDualTensorCoordinates D).val *ᵥ x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    exact hx (by simp [hzero])
  · intro hx hzero
    apply hx
    have h := congrArg (fun y => ((selfDualTensorCoordinates D)⁻¹).val *ᵥ y) hzero
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_zero] using h

namespace ConjugationLinearMap

variable [IsAffine G.X.left] {ρ : MatrixRepresentation G n}
  {σ : MatrixRepresentation G m}

/-- A supplied self-duality and a tensor-square intertwiner give a conjugation
map on every scheme test. -/
def ofSelfDualTensorIntertwiner (D : GL m k) (hD : Intertwines σ σ.dual D.val)
    {C : Matrix (m × m) n k} (hC : Intertwines ρ (σ.tensor σ) C) :
    ConjugationLinearMap ρ σ :=
  ofTensorIntertwiner (hC.comp (intertwines_selfDualTensorCoordinates D hD))

/-- The self-dual tensor-square construction preserves a nonzero supplied image. -/
theorem ofSelfDualTensorIntertwiner_eval_ne_zero_iff
    (D : GL m k) (hD : Intertwines σ σ.dual D.val)
    {C : Matrix (m × m) n k} (hC : Intertwines ρ (σ.tensor σ) C) (v : n → k) :
    MatrixLinear.eval (ofSelfDualTensorIntertwiner D hD hC).coeff (RingHom.id k) v ≠ 0 ↔
      C *ᵥ v ≠ 0 := by
  change MatrixLinear.eval (ofTensorIntertwiner
    (hC.comp (intertwines_selfDualTensorCoordinates D hD))).coeff
      (RingHom.id k) v ≠ 0 ↔ C *ᵥ v ≠ 0
  rw [ofTensorIntertwiner_eval_ne_zero_iff, ← Matrix.mulVec_mulVec]
  exact selfDualTensorCoordinates_mulVec_ne_zero_iff D _

end ConjugationLinearMap
end Langlands.GroupScheme.MatrixRepresentation
