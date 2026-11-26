import Langlands.Representation.Unitary.ConjugateContragredientStatement

/-! # The evaluation comparison for the Hermitian contragredient -/

noncomputable section

namespace Langlands.Renard.CompactRepresentation

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

private def transportDual (T : V ≃ₗ⋆[ℂ] W)
    (hT : ∀ (g : G) (x : V), T (ρ g x) = σ g (T x)) :
    SmoothDual ρ →ₗ⋆[ℂ] SmoothDual σ where
  toFun ℓ := ⟨(starLinearEquiv ℂ).toLinearMap.comp (ℓ.val.comp T.symm.toLinearMap), by
    obtain ⟨K, hK⟩ := ℓ.property
    refine ⟨K, fun k => ?_⟩
    apply LinearMap.ext
    intro y
    change starRingEnd ℂ (ℓ.val (T.symm (σ (k.val)⁻¹ y))) =
      starRingEnd ℂ (ℓ.val (T.symm y))
    have hsymm : T.symm (σ (k.val)⁻¹ y) = ρ (k.val)⁻¹ (T.symm y) := by
      apply T.injective
      simpa only [T.apply_symm_apply] using (hT (k.val)⁻¹ (T.symm y)).symm
    rw [hsymm]
    exact congrArg (fun L : Module.Dual ℂ V => starRingEnd ℂ (L (T.symm y))) (hK k)⟩
  map_add' ℓ m := by
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    change starRingEnd ℂ (ℓ.val (T.symm y) + m.val (T.symm y)) =
      starRingEnd ℂ (ℓ.val (T.symm y)) + starRingEnd ℂ (m.val (T.symm y))
    exact map_add (starRingEnd ℂ) _ _
  map_smul' c ℓ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    change starRingEnd ℂ (c * ℓ.val (T.symm y)) =
      starRingEnd ℂ c * starRingEnd ℂ (ℓ.val (T.symm y))
    exact map_mul (starRingEnd ℂ) _ _

private def transportDualEquiv (T : V ≃ₗ⋆[ℂ] W)
    (hT : ∀ (g : G) (x : V), T (ρ g x) = σ g (T x)) :
    SmoothDual ρ ≃ₗ⋆[ℂ] SmoothDual σ :=
  have hT' (g : G) (y : W) : T.symm (σ g y) = ρ g (T.symm y) := by
    apply T.injective
    simpa only [T.apply_symm_apply] using (hT g (T.symm y)).symm
  { transportDual T hT with
    invFun := transportDual T.symm hT'
    left_inv := fun ℓ => by
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      change starRingEnd ℂ (starRingEnd ℂ (ℓ.val (T.symm (T x)))) = ℓ.val x
      rw [T.symm_apply_apply, Complex.conj_conj]
    right_inv := fun ℓ => by
      apply Subtype.ext
      apply LinearMap.ext
      intro y
      change starRingEnd ℂ (starRingEnd ℂ (ℓ.val (T (T.symm y)))) = ℓ.val y
      rw [T.apply_symm_apply, Complex.conj_conj] }

/-- The natural evaluation formula gives the identification in Renard IV.2.1. -/
theorem conjugateContragredient : ConjugateContragredientStatement.{u, v} := by
  intro G _ _ _ _ _ _ V _ _ ρ _
  let T := ConjSpace.equiv V
  have hT (g : G) (x : V) : T (ρ g x) = ConjSpace.rep ρ g (T x) := by
    rw [ConjSpace.rep_apply, T.symm_apply_apply]
  let E := (ConjSpace.equiv (SmoothDual ρ)).symm.trans (transportDualEquiv T hT)
  refine ⟨Representation.Equiv.mk E (fun g => ?_), fun ℓ x => ?_⟩
  · apply LinearMap.ext
    intro ℓ
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    change starRingEnd ℂ (((ConjSpace.equiv (SmoothDual ρ)).symm ℓ).val
        (ρ g⁻¹ (T.symm y))) =
      starRingEnd ℂ (((ConjSpace.equiv (SmoothDual ρ)).symm ℓ).val
        (T.symm (ConjSpace.rep ρ g⁻¹ y)))
    rw [ConjSpace.rep_apply, T.symm_apply_apply]
  · change starRingEnd ℂ (ℓ.val (T.symm (T x))) = starRingEnd ℂ (ℓ.val x)
    rw [T.symm_apply_apply]

end Langlands.Renard.CompactRepresentation
