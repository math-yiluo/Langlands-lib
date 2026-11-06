import Langlands.AnthropicFLT.P2M.Sol.S_IsAdicComplete_of_module_finite
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Adic completeness descends through actual surjections -/

noncomputable section
universe u v w

namespace Langlands.Algebra.AdicCompleteSurjection

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

variable {S : Type v} [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Every actual surjective image local ring of a complete Noetherian local ring is complete. -/
lemma complete_of_surjective (q : R →+* S) (hq : Function.Surjective q) :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  let : Algebra R S := q.toAlgebra
  let f : R →ₗ[R] S := (Algebra.ofId R S).toLinearMap
  have hf : Function.Surjective f := hq
  let : Module.Finite R S := Module.Finite.of_surjective f hf
  let : IsPrecomplete (IsLocalRing.maximalIdeal R) S :=
    P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isPrecomplete_of_surjective
      (IsLocalRing.maximalIdeal R) f hf
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) S := {}
  have hc : IsAdicComplete ((IsLocalRing.maximalIdeal R).map q) S :=
    (IsAdicComplete.map_algebraMap_iff (S := S) (IsLocalRing.maximalIdeal R) S).mpr inferInstance
  rwa [IsLocalRing.map_maximalIdeal_of_surjective q hq] at hc

/-- The unchanged canonical completion unit is an equivalence for every such local image. -/
def completionEquivOfSurjective (q : R →+* S) (hq : Function.Surjective q) :
    letI : Algebra R S := q.toAlgebra
    S ≃ₗ[R] AdicCompletion (IsLocalRing.maximalIdeal R) S := by
  letI : Algebra R S := q.toAlgebra
  let : IsAdicComplete (IsLocalRing.maximalIdeal S) S := complete_of_surjective q hq
  let : IsAdicComplete ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) S := by
    change IsAdicComplete ((IsLocalRing.maximalIdeal R).map q) S
    rw [IsLocalRing.map_maximalIdeal_of_surjective q hq]
    infer_instance
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) S :=
    (IsAdicComplete.map_algebraMap_iff (S := S) (IsLocalRing.maximalIdeal R) S).mp inferInstance
  exact AdicCompletion.ofLinearEquiv (IsLocalRing.maximalIdeal R) S

end Langlands.Algebra.AdicCompleteSurjection
