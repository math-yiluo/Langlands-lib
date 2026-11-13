import Langlands.LinearAlgebra.ExteriorPowerTensorInjectivity

/-! # Recovering an exterior-square isomorphism from cup generators -/

noncomputable section

open scoped TensorProduct

namespace Langlands.LinearAlgebra.ExteriorSquareCoproduct

variable {R M H P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M]
  [AddCommGroup H] [Module R H] [AddCommGroup P] [Module R P]

/-- An alternating cup map is injective on the exterior square if a linear
detector identifies its monomials with their antisymmetrizations. -/
theorem cupLift_injective
    (cup : M [⋀^Fin 2]→ₗ[R] H) (detect : H →ₗ[R] ⨂[R]^2 M)
    (hdetect : ∀ v, detect (cup v) =
      exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 v)) :
    Function.Injective (exteriorPower.alternatingMapLinearEquiv cup) := by
  have hcomp : detect.comp (exteriorPower.alternatingMapLinearEquiv cup) =
      exteriorPower.toTensorPower R M 2 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] using hdetect v
  intro x y hxy
  apply exteriorPowerToTensorPower_injective R M 2
  rw [← hcomp]
  exact congrArg detect hxy

/-- The inverse of the exterior cup map, constructed from generation and a
compatible linear detector. No finite-dimensionality or characteristic
hypothesis is required. -/
def cupEquiv
    (cup : M [⋀^Fin 2]→ₗ[R] H) (detect : H →ₗ[R] ⨂[R]^2 M)
    (hgen : Function.Surjective (exteriorPower.alternatingMapLinearEquiv cup))
    (hdetect : ∀ v, detect (cup v) =
      exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 v)) :
    H ≃ₗ[R] ⋀[R]^2 M :=
  (LinearEquiv.ofBijective (exteriorPower.alternatingMapLinearEquiv cup)
    ⟨cupLift_injective cup detect hdetect, hgen⟩).symm

@[simp]
theorem cupEquiv_cup
    (cup : M [⋀^Fin 2]→ₗ[R] H) (detect : H →ₗ[R] ⨂[R]^2 M)
    (hgen : Function.Surjective (exteriorPower.alternatingMapLinearEquiv cup))
    (hdetect : ∀ v, detect (cup v) =
      exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 v))
    (v : Fin 2 → M) :
    cupEquiv cup detect hgen hdetect (cup v) = exteriorPower.ιMulti R 2 v := by
  change (LinearEquiv.ofBijective _ _).symm (cup v) = _
  rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti cup v]
  exact LinearEquiv.symm_apply_apply _ _

/-- Formulas on cup generators extend to the requested simultaneous
exterior-square and three-summand coproduct comparison. -/
theorem exists_comparison_of_cup_generators
    (cup : M [⋀^Fin 2]→ₗ[R] H)
    (hgen : Function.Surjective (exteriorPower.alternatingMapLinearEquiv cup))
    (κ : P ≃ₗ[R] H × (⨂[R]^2 M) × H)
    (p₁ p₂ m : H →ₗ[R] P)
    (hp₁ : ∀ v, κ (p₁ (cup v)) = (cup v, 0, 0))
    (hp₂ : ∀ v, κ (p₂ (cup v)) = (0, 0, cup v))
    (hm : ∀ v, κ (m (cup v)) =
      (cup v, exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 v), cup v)) :
    ∃ e : H ≃ₗ[R] ⋀[R]^2 M,
      (∀ x, κ (p₁ x) = (x, 0, 0)) ∧
      (∀ x, κ (p₂ x) = (0, 0, x)) ∧
      (∀ x, κ (m x) =
        (x, exteriorPower.toTensorPower R M 2 (e x), x)) := by
  let detect : H →ₗ[R] ⨂[R]^2 M :=
    (LinearMap.fst R (⨂[R]^2 M) H).comp
      ((LinearMap.snd R H ((⨂[R]^2 M) × H)).comp (κ.toLinearMap.comp m))
  have hdetect (v : Fin 2 → M) :
      detect (cup v) =
        exteriorPower.toTensorPower R M 2 (exteriorPower.ιMulti R 2 v) := by
    exact congrArg (fun z => z.2.1) (hm v)
  let e := cupEquiv cup detect hgen hdetect
  have h₁ : κ.toLinearMap.comp p₁ =
      (LinearMap.id : H →ₗ[R] H).prod (0 : H →ₗ[R] (⨂[R]^2 M) × H) := by
    apply (LinearMap.cancel_right hgen).mp
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearEquiv.coe_coe, LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply,
      LinearMap.zero_apply, Prod.zero_eq_mk] using hp₁ v
  have h₂ : κ.toLinearMap.comp p₂ =
      (0 : H →ₗ[R] H).prod
        ((0 : H →ₗ[R] ⨂[R]^2 M).prod (LinearMap.id : H →ₗ[R] H)) := by
    apply (LinearMap.cancel_right hgen).mp
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearEquiv.coe_coe, LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply,
      LinearMap.zero_apply] using hp₂ v
  have hₘ : κ.toLinearMap.comp m =
      (LinearMap.id : H →ₗ[R] H).prod
        (((exteriorPower.toTensorPower R M 2).comp e.toLinearMap).prod
          (LinearMap.id : H →ₗ[R] H)) := by
    apply (LinearMap.cancel_right hgen).mp
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearEquiv.coe_coe, LinearMap.prod_apply, Function.prod_apply, LinearMap.id_apply,
      e, cupEquiv_cup] using hm v
  exact ⟨e, fun x => LinearMap.congr_fun h₁ x, fun x => LinearMap.congr_fun h₂ x,
    fun x => LinearMap.congr_fun hₘ x⟩

end Langlands.LinearAlgebra.ExteriorSquareCoproduct
