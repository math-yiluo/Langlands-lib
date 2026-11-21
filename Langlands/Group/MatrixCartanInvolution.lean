import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Star.Basic
import Langlands.Group.ClosedPolarCompact

/-! # The Cartan involution of an injective matrix realization with self-adjoint range

Let `R : X →* GL (Fin n) 𝕜` be an injective homomorphism whose range is stable under conjugate
transpose, and let `a` be an element of the range. With `c = a * star a`, the formula
`R (θ x) = c * (star (R x))⁻¹ * c⁻¹` defines an involution `θ` of `X`. After conjugating by `a`,
`θ` becomes the standard Cartan involution `M ↦ (Mᴴ)⁻¹`, and its fixed points are the elements
whose conjugated matrix is unitary.
-/

noncomputable section

open scoped Matrix

set_option autoImplicit false

namespace Langlands.Group.MatrixCartanInvolution

variable {X : Type*} [Group X] {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
  (R : X →* GL (Fin n) 𝕜) (hR : Function.Injective R)
  (hstar : ∀ g ∈ R.range, star g ∈ R.range) (a : GL (Fin n) 𝕜) (ha : a ∈ R.range)

/-- The positive element `a * star a` of the range. -/
def cartanCenter : GL (Fin n) 𝕜 := a * star a

include ha hstar in
theorem cartanCenter_mem : cartanCenter a ∈ R.range :=
  R.range.mul_mem ha (hstar a ha)

theorem star_cartanCenter : star (cartanCenter a) = cartanCenter a := by
  simp [cartanCenter, star_mul]

include ha hstar in
theorem cartanTarget_mem (x : X) :
    cartanCenter a * (star (R x))⁻¹ * (cartanCenter a)⁻¹ ∈ R.range :=
  R.range.mul_mem (R.range.mul_mem (cartanCenter_mem R hstar a ha)
    (R.range.inv_mem (hstar _ ⟨x, rfl⟩))) (R.range.inv_mem (cartanCenter_mem R hstar a ha))

/-- The Cartan involution attached to `a`. -/
def cartan (x : X) : X :=
  (R.ofInjective hR).symm ⟨_, cartanTarget_mem R hstar a ha x⟩

theorem map_cartan (x : X) :
    R (cartan R hR hstar a ha x) = cartanCenter a * (star (R x))⁻¹ * (cartanCenter a)⁻¹ := by
  have h := (R.ofInjective hR).apply_symm_apply ⟨_, cartanTarget_mem R hstar a ha x⟩
  exact congrArg Subtype.val h

theorem cartan_cartan (x : X) : cartan R hR hstar a ha (cartan R hR hstar a ha x) = x := by
  apply hR
  rw [map_cartan, map_cartan, star_mul, star_mul, star_inv, star_inv, star_star,
    star_cartanCenter]
  group

theorem cartan_one : cartan R hR hstar a ha 1 = 1 := by
  apply hR
  rw [map_cartan, map_one, star_one, inv_one, mul_one, mul_inv_cancel]

/-- After conjugation by `a`, the involution is `M ↦ (star M)⁻¹`. -/
theorem conj_cartan_mul_star (x : X) :
    a⁻¹ * R (cartan R hR hstar a ha x) * a * star (a⁻¹ * R x * a) = 1 := by
  rw [map_cartan, star_mul, star_mul, star_inv]
  simp only [cartanCenter, mul_inv_rev]
  group

/-- A fixed point of the involution has unitary conjugated matrix. -/
theorem conj_mem_unitary_of_cartan_eq (x : X) (hx : cartan R hR hstar a ha x = x) :
    ((a⁻¹ * R x * a : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) ∈
      Matrix.unitaryGroup (Fin n) 𝕜 := by
  have h := conj_cartan_mul_star R hR hstar a ha x
  rw [hx] at h
  rw [Matrix.mem_unitaryGroup_iff]
  have h' := congrArg (fun g : GL (Fin n) 𝕜 => (g : Matrix (Fin n) (Fin n) 𝕜)) h
  simpa only [Units.val_mul, Units.coe_star, Units.val_one] using h'

/-- The conjugated matrices of `θ x` and `x` satisfy `M(θ x) * M(x)ᴴ = 1`. -/
theorem val_conj_cartan_mul_conjTranspose (x : X) :
    ((a⁻¹ * R (cartan R hR hstar a ha x) * a : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) *
      ((a⁻¹ * R x * a : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜)ᴴ = 1 := by
  have h := congrArg (fun g : GL (Fin n) 𝕜 => (g : Matrix (Fin n) (Fin n) 𝕜))
    (conj_cartan_mul_star R hR hstar a ha x)
  simpa only [Units.val_mul, Units.coe_star, Units.val_one, Matrix.star_eq_conjTranspose]
    using h

/-- The matrix of `θ x` in terms of the conjugate transpose of the matrix of `x⁻¹`. -/
theorem val_map_cartan (x : X) :
    ((R (cartan R hR hstar a ha x) : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) =
      ((cartanCenter a : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) *
        ((R x⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜)ᴴ *
          (((cartanCenter a)⁻¹ : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) := by
  rw [map_cartan, map_inv, ← star_inv, Units.val_mul, Units.val_mul, Units.coe_star,
    Matrix.star_eq_conjTranspose]

/-- The subgroup of elements whose matrix, conjugated by `a`, is unitary. -/
def cartanUnitary : Subgroup X :=
  Langlands.Group.MatrixPolarCompact.unitarySubgroup ((MulAut.conj a⁻¹).toMonoidHom.comp R)

theorem mem_cartanUnitary_iff (x : X) :
    x ∈ cartanUnitary R a ↔
      ((a⁻¹ * R x * a : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) ∈
        Matrix.unitaryGroup (Fin n) 𝕜 := by
  rw [cartanUnitary, Langlands.Group.MatrixPolarCompact.mem_unitarySubgroup]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem mem_cartanUnitary_of_cartan_eq (x : X) (hx : cartan R hR hstar a ha x = x) :
    x ∈ cartanUnitary R a :=
  (mem_cartanUnitary_iff R a x).mpr (conj_mem_unitary_of_cartan_eq R hR hstar a ha x hx)

theorem isCompact_cartanUnitary [TopologicalSpace X] (hRce : Topology.IsClosedEmbedding R) :
    IsCompact (cartanUnitary R a : Set X) := by
  apply Langlands.Group.MatrixPolarCompact.isCompact_unitarySubgroup
  have hconj : Topology.IsClosedEmbedding (fun g : GL (Fin n) 𝕜 => a⁻¹ * g * a) :=
    ((Homeomorph.mulRight a).isClosedEmbedding.comp (Homeomorph.mulLeft a⁻¹).isClosedEmbedding)
  convert hconj.comp hRce using 1
  funext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    Function.comp_apply]

end Langlands.Group.MatrixCartanInvolution
