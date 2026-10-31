import Langlands.Algebra.IdempotentedRingOrbitExtensionStatements

/-!
# Uniform continuity and uniqueness of the actual orbit extension

Renard I.1.3, printed p.9/PDF15. Uniform continuity of the extended
orbit and uniqueness among continuous extensions are derived consequences.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Filter Set
open scoped Topology

universe uA uM

/-- Both actual orbit maps are uniformly continuous, and the actual extended
orbit is the unique continuous extension of the original orbit. -/
theorem idempotentedRingOrbitExtension :
    IdempotentedRingOrbitExtensionTheorem.{uA, uM} := by
  intro A M _ _ _ hA hM
  have hsmul (m : M) :
      @UniformContinuous A M (⊥ : UniformSpace A) (⊥ : UniformSpace M)
        (fun a => a • m) := by
    rw [uniformContinuous_iff_le_comap]
    exact bot_le
  have horiginal : IdempotentedRingOriginalOrbitUniform A M := by
    intro m
    obtain ⟨e, he⟩ := hM m
    simpa only [Function.comp_def, mul_smul, he] using
      (@UniformContinuous.comp A A M (idempotentedRingUniformSpace A) ⊥ ⊥
        (fun a => a • m) (fun a => a * (e : A)) (hsmul m)
        (idempotentedRing_uniformContinuous_rightCoordinate e))
  have hextended : IdempotentedRingRightLimitOrbitUniform A M hM := by
    intro m
    obtain ⟨e, he⟩ := hM m
    have hformula : (fun x => IdempotentedRingRightLimitAction.act hM x m) =
        (fun x : IdempotentedRingRightLimit A => x.val e • m) :=
      funext (fun x => IdempotentedRingRightLimitAction.act_eq hA hM x m e he)
    rw [hformula]
    simpa only [Function.comp_def, IdempotentedRingRightLimit.coordinate_apply] using
      (@UniformContinuous.comp (IdempotentedRingRightLimit A) A M
        (IdempotentedRingRightLimit.uniformSpace A) ⊥ ⊥ (fun a => a • m)
        (IdempotentedRingRightLimit.coordinate e) (hsmul m)
        (IdempotentedRingRightLimit.uniformContinuous_coordinate e))
  refine ⟨horiginal, hextended, ?_⟩
  intro m
  refine ⟨@UniformContinuous.continuous (IdempotentedRingRightLimit A) M
      (IdempotentedRingRightLimit.uniformSpace A) ⊥ _ (hextended m),
    fun a => IdempotentedRingRightLimitAction.canonical_act hA hM a m, ?_⟩
  intro f hf hcanonical
  let := IdempotentedRingRightLimit.uniformSpace A
  let : UniformSpace M := ⊥
  change Continuous f at hf
  funext x
  have heq : ∀ᶠ y in 𝓝 x, f y = f x :=
    hf.continuousAt.eventually (show ∀ᶠ z in 𝓝 (f x), z = f x from by simp)
  obtain ⟨d, _, hd⟩ := (IdempotentedRingRightLimit.nhds_hasBasis hA x).mem_iff.mp heq
  obtain ⟨e, he⟩ := hM m
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {d, e}
  have hdg : d ≤ g := hg d (by simp)
  have heg : e ≤ g := hg e (by simp)
  have hgm : (g : A) • m = m := Idempotent.smul_eq_of_le heg he
  have hvalue : f (IdempotentedRingRightLimit.canonical (x.val g)) = f x := by
    apply hd
    exact x.property.2 d g hdg
  calc
    f x = f (IdempotentedRingRightLimit.canonical (x.val g)) := hvalue.symm
    _ = x.val g • m := hcanonical (x.val g)
    _ = IdempotentedRingRightLimitAction.act hM x m :=
      (IdempotentedRingRightLimitAction.act_eq hA hM x m g hgm).symm

/-! Complete unapplied checks preserve independent ring and module universes. -/

example : IdempotentedRingOrbitExtensionTheorem.{uA, uM} :=
  idempotentedRingOrbitExtension.{uA, uM}

example : IdempotentedRingOrbitExtensionTheorem.{0, 1} :=
  idempotentedRingOrbitExtension.{0, 1}

example : IdempotentedRingOrbitExtensionTheorem.{1, 0} :=
  idempotentedRingOrbitExtension.{1, 0}

end Langlands.Algebra
