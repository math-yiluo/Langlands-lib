import Langlands.Representation.Families.RenardUniversalFamilySpecializationStatement

/-!
# Renard VI.8.1 Example: proof that the fibers of the universal unramified family are twists

The specialization `ℂ ⊗[B] (B ⊗[ℂ] V)` of the universal unramified family at an unramified
character `χ` is identified with `V` by Mathlib's cancellation of the base change followed by
the left unit isomorphism; this identification intertwines the base-changed action with the
twist of `π` by `χ`.

The private helpers work over an arbitrary commutative `ℂ`-algebra `A` with an `A`-algebra
structure on `ℂ`: the identification `ℂ ⊗[A] (A ⊗[ℂ] V) ≃ V`, its value on pure tensors, and
the reduction of the intertwining property to pure tensors `c ⊗ (b ⊗ v)`.
-/

noncomputable section

open scoped TensorProduct NNReal

namespace Langlands.Renard.AlgebraicFamily

universe uA uH uG uI uV

section Fiber

variable {A : Type uA} [CommRing A] [Algebra ℂ A] [Algebra A ℂ] [IsScalarTower ℂ A ℂ]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The fiber `ℂ ⊗[A] (A ⊗[ℂ] V)` of the extended module `A ⊗[ℂ] V` along an `A`-algebra
structure on `ℂ`, identified with `V` by cancelling the base change. -/
private def fiberCancel : ℂ ⊗[A] (A ⊗[ℂ] V) ≃ₗ[ℂ] V :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℂ A ℂ ℂ V).trans (TensorProduct.lid ℂ V)

private theorem fiberCancel_tmul (c : ℂ) (b : A) (v : V) :
    fiberCancel (c ⊗ₜ[A] (b ⊗ₜ[ℂ] v)) = (algebraMap A ℂ b * c) • v := by
  change (b • c) • v = _
  rw [Algebra.smul_def]

/-- The fiber identification intertwines a base-changed action with an action on `V` as soon
as it does so on pure tensors `c ⊗ (b ⊗ v)`. -/
private theorem fiberCancel_baseChange {H : Type uH} [Group H]
    (ρ : Representation A H (A ⊗[ℂ] V)) (σ : Representation ℂ H V) (g : H)
    (h : ∀ (c : ℂ) (b : A) (v : V),
      fiberCancel (c ⊗ₜ[A] ρ g (b ⊗ₜ[ℂ] v)) = σ g (fiberCancel (c ⊗ₜ[A] (b ⊗ₜ[ℂ] v))))
    (x : ℂ ⊗[A] (A ⊗[ℂ] V)) :
    fiberCancel (baseChange ℂ ρ g x) = σ g (fiberCancel x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c y =>
    induction y using TensorProduct.inductionOn with
    | tmul b v => rw [baseChange_tmul, h]
    | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add, map_add, hy, hz, map_add, map_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Fiber

/-- VI.8.1 Example, last claim: the specialization at `χ` of the universal unramified family of
`π` is isomorphic to the twist `π ⊗ χ`, by `c ⊗ (b ⊗ v) ↦ c b(χ) v`. -/
theorem universalSpecialization : UniversalSpecializationStatement.{uG, uI, uV} := by
  intro G _ _ I ν V _ _ π χ
  let _ : AddCommGroup (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] V) :=
    TensorProduct.addCommGroup
  let _ : Module (Plancherel.unramifiedRegularFunctions ν)
      (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] V) := TensorProduct.leftModule
  let _ : Algebra (Plancherel.unramifiedRegularFunctions ν) ℂ :=
    (Plancherel.UnramifiedNormalized.evaluation ν χ).toAlgebra
  have _ : IsScalarTower ℂ (Plancherel.unramifiedRegularFunctions ν) ℂ :=
    ⟨fun c b z => by
      change (c • b).val χ * z = c * (b.val χ * z)
      rw [Subalgebra.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]⟩
  have he : ∀ (c : ℂ) (b : Plancherel.unramifiedRegularFunctions ν) (v : V),
      fiberCancel (c ⊗ₜ[Plancherel.unramifiedRegularFunctions ν] (b ⊗ₜ[ℂ] v)) =
        (c * b.val χ) • v := by
    intro c b v
    rw [fiberCancel_tmul, mul_comm]
    rfl
  refine ⟨fiberCancel, fun g x => fiberCancel_baseChange _ _ g (fun c b v => ?_) x, he⟩
  rw [Plancherel.universalUnramifiedRepresentation_tmul, he, he]
  change (c * (Plancherel.unramifiedEvaluationRegular ν g * b).val χ) • π g v =
    ((χ.val g : ℂˣ) : ℂ) • π g ((c * b.val χ) • v)
  rw [map_smul, smul_smul]
  congr 1
  change c * ((χ.val g : ℂ) * b.val χ) = (χ.val g : ℂ) * (c * b.val χ)
  ring

end Langlands.Renard.AlgebraicFamily
