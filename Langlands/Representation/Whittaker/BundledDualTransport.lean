import Langlands.Representation.Whittaker.GenericDualTransport

/-! # Bundled transport of Whittaker functionals to the actual smooth dual -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F)
  (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (E : V ≃ₗ[ℂ] SmoothDual ρ)
  (hE : ∀ g v, E (ρ (inverseTranspose (n + 1) F g) v) =
    smoothContragredient ρ g (E v))

include hE in
/-- The existing explicit functional satisfies the bundled inverse-character law. -/
theorem explicitSmoothDualFunctional_mem (ℓ : glFunctionals ψ n ρ) :
    explicitSmoothDualFunctional ρ E ℓ.val ∈
      glInverseFunctionals ψ n (smoothContragredient ρ) := by
  intro u v
  have hEsymm : E.symm (smoothContragredient ρ u.val v) =
      ρ (inverseTranspose (n + 1) F u.val) (E.symm v) := by
    apply E.injective
    rw [E.apply_symm_apply, hE, E.apply_symm_apply]
  change ℓ.val (ρ (weylLong (n + 1) F)
    (E.symm (smoothContragredient ρ u.val v))) = _
  rw [hEsymm]
  exact (dualFunctional ψ ρ ℓ).property u (E.symm v)

/-- Pullback through a supplied equivariant equivalence after long-Weyl translation,
with its actual inverse-character functional codomain. -/
def smoothDualFunctionalTransport :
    glFunctionals ψ n ρ →ₗ[ℂ] glInverseFunctionals ψ n (smoothContragredient ρ) where
  toFun ℓ := ⟨explicitSmoothDualFunctional ρ E ℓ.val,
    explicitSmoothDualFunctional_mem ψ ρ E hE ℓ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem smoothDualFunctionalTransport_val (ℓ : glFunctionals ψ n ρ) :
    (smoothDualFunctionalTransport ψ ρ E hE ℓ).val =
      explicitSmoothDualFunctional ρ E ℓ.val := rfl

@[simp] theorem smoothDualFunctionalTransport_apply (ℓ : glFunctionals ψ n ρ)
    (v : SmoothDual ρ) :
    (smoothDualFunctionalTransport ψ ρ E hE ℓ).val v =
      ℓ.val (ρ (weylLong (n + 1) F) (E.symm v)) := rfl

/-- Nonvanishing is preserved by the actual construction. -/
theorem smoothDualFunctionalTransport_ne_zero (ℓ : glFunctionals ψ n ρ)
    (hℓ : ℓ.val ≠ 0) : (smoothDualFunctionalTransport ψ ρ E hE ℓ).val ≠ 0 :=
  explicitSmoothDualFunctional_ne_zero ρ E ℓ.val hℓ

end Langlands.Whittaker
