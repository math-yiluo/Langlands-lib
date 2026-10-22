import Langlands.LocalField.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The inverse-transpose realization of a generic smooth contragredient

The proposition records the irreducible Whittaker-type specialization used in
JPSS (1983), Section 2.1. No theorem is asserted by defining this target.
-/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- For a generic irreducible admissible representation, inverse transpose
realizes the smooth contragredient, which is generic for the inverse character. -/
def GenericContragredientStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ),
      Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ → Representation.IsIrreducible ρ →
      (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧
        ∀ g : Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier,
          (∀ i j, j < i → g.val i j = 0) →
          (∀ i, g.val i i = 1) →
          ∀ v, ℓ (ρ g v) = (∏ i : Fin n, ψ (g.val i.castSucc i.succ)) * ℓ v) →
      let invTranspose :=
        fun g : Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier =>
          Matrix.GeneralLinearGroup.mkOfDetNeZero (g⁻¹).val.transpose
            (by
              simpa only [Matrix.det_transpose] using
                Matrix.GeneralLinearGroup.det_ne_zero (g⁻¹))
      (∃ E : V ≃ₗ[ℂ] SmoothDual ρ, ∀ g v,
        E (ρ (invTranspose g) v) = smoothContragredient ρ g (E v)) ∧
      (∃ ℓ : Module.Dual ℂ (SmoothDual ρ), ℓ ≠ 0 ∧
        ∀ g : Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier,
          (∀ i j, j < i → g.val i j = 0) →
          (∀ i, g.val i i = 1) →
          ∀ v, ℓ (smoothContragredient ρ g v) =
            (∏ i : Fin n, ψ⁻¹ (g.val i.castSucc i.succ)) * ℓ v)

end Langlands
