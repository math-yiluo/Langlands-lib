import Langlands.Algebra.RenardSurjectiveLocalizationStatements
import Langlands.Algebra.RenardEndomorphismLocalizationKernelProof

/-! # Surjective canonical localization map: proof for the actual quotient -/

set_option autoImplicit false

universe u v

namespace Langlands.Renard.EndomorphismLocalization

section

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- A surjective canonical map identifies the actual localization uniquely
with the actual power-kernel quotient, compatibly with both canonical maps
and endomorphisms. -/
theorem existsUnique_quotientEquiv_of_surjective (a : Module.End R V)
    (ha : Function.Surjective (iota a)) :
    ∃! e : Localized a ≃ₗ[R] PowerKernelQuotient a,
      e.toLinearMap.comp (localizedEnd a) =
          (quotientEnd a).comp e.toLinearMap ∧
        e.toLinearMap.comp (iota a) = quotientProjection a := by
  classical
  have hker : powerKernel a = LinearMap.ker (iota a) := by
    rw [powerKernel_def, ker_iota_eq_iSup]
  let f : PowerKernelQuotient a →ₗ[R] Localized a :=
    (powerKernel a).liftQ (iota a) hker.le
  have hinj : Function.Injective f :=
    LinearMap.ker_eq_bot.mp ((powerKernel a).ker_liftQ_eq_bot' (iota a) hker)
  have hsur : Function.Surjective f := by
    intro x
    obtain ⟨z, rfl⟩ := ha x
    exact ⟨quotientProjection a z, rfl⟩
  let d : PowerKernelQuotient a ≃ₗ[R] Localized a :=
    LinearEquiv.ofBijective f ⟨hinj, hsur⟩
  let e : Localized a ≃ₗ[R] PowerKernelQuotient a := d.symm
  have he (z : V) : e (iota a z) = quotientProjection a z := by
    change d.symm (d (quotientProjection a z)) = quotientProjection a z
    exact d.symm_apply_apply _
  have hop : e.toLinearMap.comp (localizedEnd a) =
      (quotientEnd a).comp e.toLinearMap := by
    ext x
    obtain ⟨z, rfl⟩ := ha x
    change e (localizedEnd a (iota a z)) = quotientEnd a (e (iota a z))
    rw [← iota_intertwines, he, he, quotientEnd_projection]
  have hcomp : e.toLinearMap.comp (iota a) = quotientProjection a := by
    ext z
    exact he z
  refine ⟨e, ⟨hop, hcomp⟩, ?_⟩
  intro e' he'
  apply LinearEquiv.ext
  intro x
  obtain ⟨z, rfl⟩ := ha x
  calc
    e' (iota a z) = quotientProjection a z :=
      congrArg (fun g : V →ₗ[R] PowerKernelQuotient a => g z) he'.2
    _ = e (iota a z) := (he z).symm

end

/-- The complete ring-general corollary and its explicit field specialization. -/
theorem surjectiveIotaQuotientStatements : SurjectiveIotaQuotientStatements.{u, v} := by
  constructor
  · intro R _ V _ _ a ha
    exact existsUnique_quotientEquiv_of_surjective a ha
  · intro k _ V _ _ a ha
    exact existsUnique_quotientEquiv_of_surjective a ha

end Langlands.Renard.EndomorphismLocalization
