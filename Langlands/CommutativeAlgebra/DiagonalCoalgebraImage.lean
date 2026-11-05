import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-! # Homogeneous coefficients in images of diagonal coalgebras -/

noncomputable section

universe u v w

open TensorProduct

namespace Langlands.CommutativeAlgebra.DiagonalCoalgebraImage

variable {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M]
  {B : Type w} [CommRing B] [Bialgebra R B]

/-- Coefficient extraction as an `R`-linear map. -/
def coefficient (m : M) : AddMonoidAlgebra R M →ₗ[R] R :=
  (Finsupp.lapply m).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

omit [AddCommMonoid M] in
@[simp] theorem coefficient_apply (m : M) (x : AddMonoidAlgebra R M) :
    coefficient m x = x.coeff m := rfl

/-- Contract the first factor against the coefficient in degree `m`. -/
def contract (m : M) :
    AddMonoidAlgebra R M ⊗[R] AddMonoidAlgebra R M →ₗ[R] AddMonoidAlgebra R M :=
  (TensorProduct.lid R _).toLinearMap.comp ((coefficient m).rTensor _)

@[simp] theorem contract_tmul (m : M) (x y : AddMonoidAlgebra R M) :
    contract m (x ⊗ₜ[R] y) = x.coeff m • y := by
  simp [contract]

theorem contract_comul (m : M) (x : AddMonoidAlgebra R M) :
    contract m (Coalgebra.comul x) = AddMonoidAlgebra.single m (x.coeff m) := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      hx, hy, AddMonoidAlgebra.single_add]
  | single n r =>
    simp only [AddMonoidAlgebra.comul_single]
    simp only [CommSemiring.comul_apply, TensorProduct.map_tmul,
      AddMonoidAlgebra.lsingle_apply]
    rw [contract_tmul]
    by_cases h : n = m
    · subst n
      simp
    · simp [AddMonoidAlgebra.coeff_single, Ne.symm h]

/-- The image of a bialgebra homomorphism into a monoid algebra contains
each homogeneous coefficient of each of its elements. -/
theorem single_coefficient_mem_range (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (b : B) (m : M) :
    AddMonoidAlgebra.single m ((φ b).coeff m) ∈ φ.toAlgHom.range := by
  have h : ∀ z : B ⊗[R] B,
      contract m (TensorProduct.map φ.toLinearMap φ.toLinearMap z) ∈
        φ.toAlgHom.range := by
    intro z
    induction z with
    | tmul x y =>
      rw [TensorProduct.map_tmul, contract_tmul]
      exact φ.toAlgHom.range.smul_mem (φ.toAlgHom.mem_range_self y) _
    | add x y hx hy =>
      rw [map_add, map_add]
      exact φ.toAlgHom.range.add_mem hx hy
  have hb := h (Coalgebra.comul b)
  change contract m (TensorProduct.map (φ : B →ₗ[R] AddMonoidAlgebra R M)
    (φ : B →ₗ[R] AddMonoidAlgebra R M) (Coalgebra.comul b)) ∈ φ.toAlgHom.range at hb
  rw [CoalgHomClass.map_comp_comul_apply, contract_comul] at hb
  exact hb

end Langlands.CommutativeAlgebra.DiagonalCoalgebraImage
