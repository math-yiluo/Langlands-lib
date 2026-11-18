import Langlands.GroupScheme.Cohomology.RegularCochains
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Transport of regular actions and cochains through coefficient equivalences -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}}
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Extend a base-module equivalence to every test-algebra coefficient module. -/
def coefficientPointEquiv (e : M ≃ₗ[R] N) (A : CommAlgCat.{u} R) :
    ModulePoints M A ≃ₗ[A] ModulePoints N A :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e

@[simp]
theorem coefficientPointEquiv_tmul (e : M ≃ₗ[R] N) (A : CommAlgCat.{u} R)
    (a : A) (m : M) : coefficientPointEquiv e A (a ⊗ₜ[R] m) = a ⊗ₜ[R] e m := rfl

@[simp]
theorem coefficientPointEquiv_symm_tmul (e : M ≃ₗ[R] N) (A : CommAlgCat.{u} R)
    (a : A) (n : N) :
    (coefficientPointEquiv e A).symm (a ⊗ₜ[R] n) = a ⊗ₜ[R] e.symm n := rfl

/-- The extended equivalence commutes with every change of test algebra. -/
theorem coefficientPointEquiv_naturality (e : M ≃ₗ[R] N)
    {A B : CommAlgCat.{u} R} (f : A ⟶ B) (x : ModulePoints M A) :
    modulePointMap N f (coefficientPointEquiv e A x) =
      coefficientPointEquiv e B (modulePointMap M f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {H : GroupScheme (Spec R)}

/-- Transfer the pointwise action through an actual coefficient equivalence. -/
def ModuleRepresentation.congrAction (ρ : ModuleRepresentation M H)
    (e : M ≃ₗ[R] N) (A : CommAlgCat.{u} R) :
    H.affinePoints A →* (ModulePoints N A ≃ₗ[A] ModulePoints N A) where
  toFun h := (coefficientPointEquiv e A).symm.trans
    ((ρ.action A h).trans (coefficientPointEquiv e A))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp only [map_one, LinearEquiv.trans_apply]
    exact (coefficientPointEquiv e A).apply_symm_apply x
  map_mul' h k := by
    apply LinearEquiv.ext
    intro x
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

/-- Transport a natural module representation through a base-linear coefficient
equivalence without changing the acting group. -/
def ModuleRepresentation.congr (ρ : ModuleRepresentation M H) (e : M ≃ₗ[R] N) :
    ModuleRepresentation N H where
  action A := ρ.congrAction e A
  naturality {A B} f h x := by
    change modulePointMap N f
        (coefficientPointEquiv e A (ρ.action A h ((coefficientPointEquiv e A).symm x))) =
      coefficientPointEquiv e B
        (ρ.action B (H.affinePointMap f h)
          ((coefficientPointEquiv e B).symm (modulePointMap N f x)))
    rw [coefficientPointEquiv_naturality, ρ.naturality]
    apply congrArg (fun y => coefficientPointEquiv e B (ρ.action B (H.affinePointMap f h) y))
    apply (coefficientPointEquiv e B).injective
    rw [LinearEquiv.apply_symm_apply, ← coefficientPointEquiv_naturality,
      LinearEquiv.apply_symm_apply]

/-- The extended coefficient equivalence intertwines the transported action. -/
theorem ModuleRepresentation.congr_action (ρ : ModuleRepresentation M H)
    (e : M ≃ₗ[R] N) (A : CommAlgCat.{u} R) (h : H.affinePoints A)
    (x : ModulePoints M A) :
    (ρ.congr e).action A h (coefficientPointEquiv e A x) =
      coefficientPointEquiv e A (ρ.action A h x) := by
  change coefficientPointEquiv e A
    (ρ.action A h ((coefficientPointEquiv e A).symm (coefficientPointEquiv e A x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Transport regular one-cochain values through a base-module equivalence. -/
def OneCochain.congr (c : OneCochain M H) (e : M ≃ₗ[R] N) : OneCochain N H where
  value A h := coefficientPointEquiv e A (c.value A h)
  naturality f h := by rw [coefficientPointEquiv_naturality, c.naturality]

/-- Transport regular two-cochain values through a base-module equivalence. -/
def TwoCochain.congr (c : TwoCochain M H) (e : M ≃ₗ[R] N) : TwoCochain N H where
  value A h k := coefficientPointEquiv e A (c.value A h k)
  naturality f h k := by rw [coefficientPointEquiv_naturality, c.naturality]

/-- Coefficient transport preserves the one-cocycle equation. -/
theorem OneCochain.congr_isCocycle (ρ : ModuleRepresentation M H)
    (e : M ≃ₗ[R] N) (c : OneCochain M H) (hc : c.IsCocycle ρ) :
    (c.congr e).IsCocycle (ρ.congr e) := by
  intro A h k
  simpa only [OneCochain.congr, ModuleRepresentation.congr,
    ModuleRepresentation.congrAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add] using
      congrArg (coefficientPointEquiv e A) (hc A h k)

/-- Coefficient transport preserves the two-cocycle equation. -/
theorem TwoCochain.congr_isCocycle (ρ : ModuleRepresentation M H)
    (e : M ≃ₗ[R] N) (c : TwoCochain M H) (hc : c.IsCocycle ρ) :
    (c.congr e).IsCocycle (ρ.congr e) := by
  intro A h k l
  simpa only [TwoCochain.congr, ModuleRepresentation.congr,
    ModuleRepresentation.congrAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add] using
      congrArg (coefficientPointEquiv e A) (hc A h k l)

/-- A one-coboundary primitive transports by the given base-module equivalence. -/
theorem OneCochain.congr_isCoboundary (ρ : ModuleRepresentation M H)
    (e : M ≃ₗ[R] N) (c : OneCochain M H) (hc : c.IsCoboundary ρ) :
    (c.congr e).IsCoboundary (ρ.congr e) := by
  obtain ⟨m, hm⟩ := hc
  refine ⟨e m, fun A h => ?_⟩
  simpa only [OneCochain.congr, ModuleRepresentation.congr,
    ModuleRepresentation.congrAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, coefficientPointEquiv_symm_tmul,
    LinearEquiv.symm_apply_apply, map_sub, coefficientPointEquiv_tmul] using
      congrArg (coefficientPointEquiv e A) (hm A h)

/-- A natural one-cochain coboundary primitive transports with its coefficients. -/
theorem TwoCochain.congr_isCoboundary (ρ : ModuleRepresentation M H)
    (e : M ≃ₗ[R] N) (c : TwoCochain M H) (hc : c.IsCoboundary ρ) :
    (c.congr e).IsCoboundary (ρ.congr e) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨b.congr e, fun A h k => ?_⟩
  simpa only [OneCochain.congr, TwoCochain.congr, ModuleRepresentation.congr,
    ModuleRepresentation.congrAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add] using
      congrArg (coefficientPointEquiv e A) (hb A h k)

end Langlands.GroupScheme.Cohomology
