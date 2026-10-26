import Langlands.Shimura.PEL.TracePairing
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Algebraic and bilinear similitudes of the trace pairing -/

noncomputable section

universe u v w

namespace Langlands.Shimura.PEL

section SelfModule

variable {A : Type u} [Ring A]

/-- A left-linear self-map of the regular module is right multiplication. -/
theorem selfEquiv_apply (e : A ≃ₗ[A] A) (x : A) : e x = x * e 1 := by
  simpa only [smul_eq_mul, mul_one] using e.map_smul x (1 : A)

/-- The unit recovered from a left-linear automorphism of the regular module. -/
def selfEquivUnit (e : A ≃ₗ[A] A) : Aˣ where
  val := e 1
  inv := e.symm 1
  val_inv := (selfEquiv_apply e.symm (e 1)).symm.trans (e.symm_apply_apply 1)
  inv_val := (selfEquiv_apply e (e.symm 1)).symm.trans (e.apply_symm_apply 1)

@[simp] theorem selfEquivUnit_val (e : A ≃ₗ[A] A) :
    (selfEquivUnit e : A) = e 1 := rfl

end SelfModule

section Similitudes

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (σ : AlgebraInvolution R A) (ψ : LinearMap.BilinForm R A)
    (hψ : ψ.Nondegenerate)
    (hadj : ∀ b x y : A, ψ (x * b) y = ψ x (y * σ b))

include hψ hadj

/-- The right-multiplication form equation is exactly the algebraic similitude
equation for the right-action adjoint. -/
theorem rightMul_similitude_iff (g : Aˣ) (c : Rˣ) :
    (∀ x y : A, ψ (x * (g : A)) (y * (g : A)) = (c : R) * ψ x y) ↔
      (g, c) ∈ σ.similitudes := by
  rw [σ.mem_similitudes_iff]
  constructor
  · intro hg
    apply sub_eq_zero.mp
    apply hψ.2
    intro x
    rw [map_sub]
    have h := hg x 1
    rw [one_mul, hadj] at h
    rw [h]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    exact sub_self _
  · intro hg x y
    rw [hadj, mul_assoc, hg, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one, map_smul, smul_eq_mul]

/-- Right multiplication realizes the algebraic similitude group in the
bilinear group. Composition requires the opposite of the source group. -/
def algebraicToBilinear :
    σ.similitudesᵐᵒᵖ →* bilinearSimilitudes A ψ where
  toFun g :=
    ⟨((g.unop.val.1).mulRightLinearEquiv A, g.unop.val.2),
      (rightMul_similitude_iff σ ψ hψ hadj _ _).mpr g.unop.property⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · ext x
      exact mul_one x
    · rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Prod.ext
    · ext x
      exact (mul_assoc x (h.unop.val.1 : A) (g.unop.val.1 : A)).symm
    · exact mul_comm h.unop.val.2 g.unop.val.2

/-- Every left-linear bilinear similitude comes from right multiplication by
its value at one, with the same multiplier. -/
def bilinearToAlgebraic (g : bilinearSimilitudes A ψ) : σ.similitudesᵐᵒᵖ :=
  MulOpposite.op
    ⟨(selfEquivUnit g.val.1, g.val.2), by
      apply (rightMul_similitude_iff σ ψ hψ hadj _ _).mp
      intro x y
      change ψ (x * g.val.1 1) (y * g.val.1 1) = (g.val.2 : R) * ψ x y
      rw [← selfEquiv_apply, ← selfEquiv_apply]
      exact g.property x y⟩

/-- The actual group equivalence, retaining the opposite convention and
preserving the recorded multiplier. -/
def algebraicBilinearEquiv :
    σ.similitudesᵐᵒᵖ ≃* bilinearSimilitudes A ψ where
  toFun := algebraicToBilinear σ ψ hψ hadj
  invFun := bilinearToAlgebraic σ ψ hψ hadj
  left_inv g := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      exact one_mul (g.unop.val.1 : A)
    · rfl
  right_inv g := by
    apply Subtype.ext
    apply Prod.ext
    · ext x
      exact (selfEquiv_apply g.val.1 x).symm
    · rfl
  map_mul' := (algebraicToBilinear σ ψ hψ hadj).map_mul

@[simp] theorem algebraicBilinearEquiv_apply (g : σ.similitudesᵐᵒᵖ) (x : A) :
    (algebraicBilinearEquiv σ ψ hψ hadj g).val.1 x = x * (g.unop.val.1 : A) := rfl

@[simp] theorem algebraicBilinearEquiv_multiplier (g : σ.similitudesᵐᵒᵖ) :
    bilinearSimilitudes.multiplier ψ (algebraicBilinearEquiv σ ψ hψ hadj g) =
      σ.multiplier g.unop := rfl

end Similitudes
end Langlands.Shimura.PEL

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (β : Aˣ)
    (hβ : D.involution (β : A) = -(β : A))

/-- The rational PEL trace-form similitudes are the opposite of the actual
beta-adjoint algebraic similitudes, via right multiplication. -/
def traceSimilitudesEquiv :
    (D.tracePairingAdjoint β hβ).similitudesᵐᵒᵖ ≃*
      PEL.bilinearSimilitudes A (D.tracePairing β) :=
  PEL.algebraicBilinearEquiv _ _ (D.tracePairing_nondegenerate β)
    (D.tracePairing_right β hβ)

@[simp] theorem traceSimilitudesEquiv_apply
    (g : (D.tracePairingAdjoint β hβ).similitudesᵐᵒᵖ) (x : A) :
    (D.traceSimilitudesEquiv β hβ g).val.1 x = x * (g.unop.val.1 : A) := rfl

@[simp] theorem traceSimilitudesEquiv_multiplier
    (g : (D.tracePairingAdjoint β hβ).similitudesᵐᵒᵖ) :
    PEL.bilinearSimilitudes.multiplier (D.tracePairing β)
      (D.traceSimilitudesEquiv β hβ g) =
        (D.tracePairingAdjoint β hβ).multiplier g.unop := rfl

end Langlands.Shimura.CentralSimpleUnitaryData
