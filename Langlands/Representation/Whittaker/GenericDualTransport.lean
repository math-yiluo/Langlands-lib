import Langlands.Representation.Whittaker.DualTransform
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Explicit Whittaker-functional transport to the smooth dual

The construction takes a supplied linear equivalence to the actual smooth dual.
Its covariance law additionally requires inverse-transpose equivariance. It does
not construct that equivalence or prove the Gelfand–Kazhdan theorem.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear
open scoped BigOperators

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Weyl translation followed by pullback through a supplied equivalence to the
actual smooth dual. Equivariance of the equivalence is a separate hypothesis. -/
def explicitSmoothDualFunctional (E : V ≃ₗ[ℂ] SmoothDual ρ)
    (ℓ : Module.Dual ℂ V) : Module.Dual ℂ (SmoothDual ρ) :=
  (ℓ.comp (ρ (weylLong (n + 1) F))).comp E.symm.toLinearMap

@[simp] theorem explicitSmoothDualFunctional_apply
    (E : V ≃ₗ[ℂ] SmoothDual ρ) (ℓ : Module.Dual ℂ V) (v : SmoothDual ρ) :
    explicitSmoothDualFunctional ρ E ℓ v =
      ℓ (ρ (weylLong (n + 1) F) (E.symm v)) := rfl

/-- The constructed functional preserves nonvanishing. -/
theorem explicitSmoothDualFunctional_ne_zero
    (E : V ≃ₗ[ℂ] SmoothDual ρ) (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) :
    explicitSmoothDualFunctional ρ E ℓ ≠ 0 := by
  intro hz
  apply hℓ
  ext v
  have hv := LinearMap.congr_fun hz (E (ρ (weylLong (n + 1) F) v))
  simp only [explicitSmoothDualFunctional_apply, E.symm_apply_apply,
    LinearMap.zero_apply] at hv
  rw [← Module.End.mul_apply, ← map_mul, weylLong_mul_self, map_one,
    Module.End.one_apply] at hv
  exact hv

omit [TopologicalSpace F] in
/-- The adjacent-entry product reverses the character under Weyl reflection. -/
theorem reflectedUnipotent_character_product (ψ : AddChar F ℂ)
    (u : upperUnipotent (n + 1) F) :
    (∏ i : Fin n, ψ ((reflectedUnipotent u).val.val i.castSucc i.succ)) =
      ∏ i : Fin n, ψ⁻¹ (u.val.val i.castSucc i.succ) := by
  simp only [reflectedUnipotent_adjacent, ← AddChar.inv_apply]
  exact Equiv.prod_comp Fin.revPerm (fun i : Fin n => ψ⁻¹ (u.val.val i.castSucc i.succ))

variable [IsTopologicalRing F]

/-- Explicit upper-unitriangular covariance on the genuine smooth dual.
Only the displayed equivariance of the supplied equivalence is used. -/
theorem explicitSmoothDualFunctional_covariance
    (E : V ≃ₗ[ℂ] SmoothDual ρ)
    (hE : ∀ g v, E (ρ (inverseTranspose (n + 1) F g) v) =
      smoothContragredient ρ g (E v))
    (ψ : AddChar F ℂ) (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ g : Langlands.GeneralLinear (n + 1) F,
      (∀ i j, j < i → g.val i j = 0) → (∀ i, g.val i i = 1) →
      ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hupper : ∀ i j, j < i → g.val i j = 0) (hdiag : ∀ i, g.val i i = 1)
    (v : SmoothDual ρ) :
    explicitSmoothDualFunctional ρ E ℓ (smoothContragredient ρ g v) =
      (∏ i : Fin n, ψ⁻¹ (g.val i.castSucc i.succ)) *
        explicitSmoothDualFunctional ρ E ℓ v := by
  let u : upperUnipotent (n + 1) F := ⟨g, ⟨fun _ _ hij => hupper _ _ hij, hdiag⟩⟩
  have hEsymm : E.symm (smoothContragredient ρ g v) =
      ρ (inverseTranspose (n + 1) F g) (E.symm v) := by
    apply E.injective
    rw [E.apply_symm_apply, hE, E.apply_symm_apply]
  have hweyl : weylLong (n + 1) F * inverseTranspose (n + 1) F g =
      (reflectedUnipotent u).val * weylLong (n + 1) F := by
    simp only [reflectedUnipotent_val, u, mul_assoc, weylLong_mul_self, mul_one]
  rw [explicitSmoothDualFunctional_apply, hEsymm, ← Module.End.mul_apply,
    ← map_mul, hweyl, map_mul, Module.End.mul_apply]
  rw [hℓ (reflectedUnipotent u).val
    (fun _ _ hij => (reflectedUnipotent u).property.1 hij)
    (reflectedUnipotent u).property.2]
  rw [reflectedUnipotent_character_product]
  rfl

end Langlands.Whittaker
