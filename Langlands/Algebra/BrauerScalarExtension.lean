import Langlands.Algebra.BrauerGroup

/-! # Scalar extension on the actual Brauer group -/

noncomputable section

namespace Langlands.Brauer

universe u

open scoped TensorProduct

variable {K : Type u} [Field K]
variable (L : Type u) [Field L] [Algebra K L]

/-- Scalar extension commutes with actual positive-size matrix algebras. -/
def baseChangeMatrixEquiv (A : CSA.{u, u} K) (n : ℕ) :
    L ⊗[K] Matrix (Fin n) (Fin n) A ≃ₐ[L]
      Matrix (Fin n) (Fin n) (L ⊗[K] A) :=
  (Algebra.TensorProduct.congr (matrixOneEquiv (K := L) L).symm
    (AlgEquiv.refl : Matrix (Fin n) (Fin n) A ≃ₐ[K]
      Matrix (Fin n) (Fin n) A)).trans <|
  (Matrix.kroneckerTMulAlgEquiv (Fin 1) (Fin n) K L L A).trans <|
  Matrix.reindexAlgEquiv L (L ⊗[K] A) (Equiv.uniqueProd (Fin n) (Fin 1))

theorem equivalent_baseChange {A B : CSA.{u, u} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (baseChange L A) (baseChange L B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨(baseChangeMatrixEquiv L A n).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans <|
    baseChangeMatrixEquiv L B m⟩⟩

/-- Extending a tensor product is tensoring the scalar extensions over the new field. -/
def baseChangeTensorEquiv (A B : CSA.{u, u} K) :
    (L ⊗[K] A) ⊗[L] (L ⊗[K] B) ≃ₐ[L] L ⊗[K] (A ⊗[K] B) :=
  (Algebra.TensorProduct.tensorTensorTensorComm K K L L L A L B).trans <|
    Algebra.TensorProduct.congr (Algebra.TensorProduct.lid L L)
      (AlgEquiv.refl : A ⊗[K] B ≃ₐ[K] A ⊗[K] B)

@[simp] theorem baseChangeTensorEquiv_tmul (A B : CSA.{u, u} K)
    (l m : L) (a : A) (b : B) :
    baseChangeTensorEquiv L A B ((l ⊗ₜ[K] a) ⊗ₜ[L] (m ⊗ₜ[K] b)) =
      (l * m) ⊗ₜ[K] (a ⊗ₜ[K] b) := rfl

/-- Scalar extension as an additive homomorphism of the actual Brauer groups. -/
def scalarExtension : BrauerGroup.{u, u} K →+ BrauerGroup.{u, u} L where
  toFun := Quotient.lift (fun A => classOf (baseChange L A))
    (fun _ _ h => Quotient.sound (equivalent_baseChange L h))
  map_zero' := classOf_eq_of_algEquiv (Algebra.TensorProduct.rid K L L)
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
    exact classOf_eq_of_algEquiv (baseChangeTensorEquiv L A B).symm

@[simp] theorem scalarExtension_classOf (A : CSA.{u, u} K) :
    scalarExtension L (classOf A) = classOf (baseChange L A) := rfl

/-- Extending by the ground field uses the actual left unit equivalence. -/
theorem scalarExtension_self : scalarExtension K = AddMonoidHom.id (BrauerGroup K) := by
  ext a
  induction a using Quotient.inductionOn with | _ A =>
  exact classOf_eq_of_algEquiv (Algebra.TensorProduct.lid K A)

variable (M : Type u) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The actual algebra identification for iterated field extension. -/
def baseChangeTowerEquiv (A : CSA.{u, u} K) :
    M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A :=
  (Algebra.TensorProduct.assoc K L M M L A).symm.trans <|
  Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L M M)
    (AlgEquiv.refl : A ≃ₐ[K] A)

@[simp] theorem baseChangeTowerEquiv_tmul (A : CSA.{u, u} K)
    (m : M) (l : L) (a : A) :
    baseChangeTowerEquiv L M A (m ⊗ₜ[L] (l ⊗ₜ[K] a)) = (l • m) ⊗ₜ[K] a := by
  simp [baseChangeTowerEquiv, Algebra.smul_def, mul_comm]

/-- Scalar extension is compatible with every actual tower of field extensions. -/
theorem scalarExtension_tower :
    (scalarExtension M (K := L)).comp (scalarExtension L (K := K)) =
      scalarExtension M (K := K) := by
  ext a
  induction a using Quotient.inductionOn with | _ A =>
  exact classOf_eq_of_algEquiv (baseChangeTowerEquiv L M A)

end Langlands.Brauer
