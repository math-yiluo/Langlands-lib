import Langlands.ClassField.Global.CyclicIdeleClassHerbrandQuotientStatement
import Langlands.ClassField.Global.CyclicUnitHerbrandQuotient
import Langlands.ClassField.Global.IntegralIdeleClassQuotientFiniteStatement
import Langlands.Cohomology.HerbrandQuotient
import Langlands.ClassField.Global.IntegralIdeleClassQuotientFinite
import Langlands.ClassField.Global.IntegralIdeleUnitExact
import Langlands.ClassField.Global.IntegralIdeleHerbrand
import Langlands.ClassField.Global.ArchimedeanLocalHerbrand

/-! # Assembly of the idele-class Herbrand quotient from arithmetic inputs -/

noncomputable section

universe u v

namespace Langlands.ClassField.Global

open CategoryTheory Langlands.Cohomology.Herbrand

/-- Conditional assembly on the actual coefficient groups. The arithmetic inputs remain explicit. -/
theorem cyclicIdeleClassHerbrandQuotient_of_integral_data
    (hunit : CyclicUnitHerbrandQuotient.{u,v})
    (hfinite : IntegralIdeleClassQuotientFinite.{v})
    (hexact : ∀ (E : Type v) [Field E] [NumberField E],
      Function.Injective (ringIntegerUnitsToIntegralIdeles E) ∧
        (integralIdelesToClasses E).ker = (ringIntegerUnitsToIntegralIdeles E).range)
    (hintegral : ∀ (F : Type u) [Field F] [NumberField F]
      (E : Type v) [Field E] [NumberField E] [Algebra F E]
      [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
      Finite (integralIdeleCohomology F E 1) ∧
        Finite (integralIdeleCohomology F E 2) ∧
        Nat.card (integralIdeleCohomology F E 2) =
          archimedeanHerbrandFactor F E * Nat.card (integralIdeleCohomology F E 1)) :
    CyclicIdeleClassHerbrandQuotient.{u,v} := by
  intro F _ _ E _ _ _ _ _
  let S := ShortComplex.mk (ringIntegerUnitsToIntegralIdelesHom F E)
    (integralIdelesToClassesHom F E)
    (ringIntegerUnitsToIntegralIdelesHom_comp_integralIdelesToClassesHom F E)
  obtain ⟨hi, hk⟩ := hexact E
  have hS : S.ShortExact := by
    refine repShortExact_of_values S ?_ ?_ (integralIdelesToClassesHom_surjective F E)
    · intro a b hab
      exact congrArg Additive.ofMul (hi (congrArg Additive.toMul hab))
    · intro x hx
      have hx' : (@Additive.toMul _ x) ∈ (integralIdelesToClasses E).ker :=
        congrArg Additive.toMul hx
      rw [hk] at hx'
      obtain ⟨a, ha⟩ := hx'
      exact ⟨Additive.ofMul a, congrArg Additive.ofMul ha⟩
  obtain ⟨hU1, hU2, hU⟩ := hunit F E
  obtain ⟨hJ1, hJ2, hJ⟩ := hintegral F E
  have hJq : HasHerbrandQuotient (integralIdeleRepresentation F E)
      (archimedeanHerbrandFactor F E) :=
    (hasHerbrandQuotient_natCast_iff _ _).mpr ⟨hJ1, hJ2, hJ⟩
  have hn : (Module.finrank F E : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := E)).ne'
  have hD : (archimedeanHerbrandFactor F E : ℚ) ≠ 0 := hJq.pos.ne'
  have hUq : HasHerbrandQuotient (ringIntegerUnitsRepresentation F E)
      ((archimedeanHerbrandFactor F E : ℚ) / Module.finrank F E) := by
    refine ⟨hU1, hU2, ?_⟩
    have hU' : (Module.finrank F E : ℚ) *
        Nat.card (groupCohomology (ringIntegerUnitsRepresentation F E) 2) =
        archimedeanHerbrandFactor F E *
          Nat.card (groupCohomology (ringIntegerUnitsRepresentation F E) 1) := by
      exact_mod_cast hU
    apply (mul_left_cancel₀ hn)
    calc
      _ = (archimedeanHerbrandFactor F E : ℚ) *
          Nat.card (groupCohomology (ringIntegerUnitsRepresentation F E) 1) := hU'
      _ = _ := by field_simp
  have hCinf := HasHerbrandQuotient.of_shortExact_right hS hUq hJq
  have hCinf' : HasHerbrandQuotient (integralIdeleClassRepresentation F E)
      (Module.finrank F E) := by
    convert hCinf using 1
    field_simp
  let : Finite (IntegralIdeleClassQuotient E) := hfinite E
  let : Finite (integralIdeleClassQuotientRepresentation F E) := by
    change Finite (Additive (IntegralIdeleClassQuotient E))
    infer_instance
  have hQ : HasHerbrandQuotient (integralIdeleClassQuotientRepresentation F E) 1 :=
    hasHerbrandQuotient_of_finite _
  have hC := HasHerbrandQuotient.of_shortExact
    (integralIdeleClassSequence_shortExact F E) hCinf' hQ
  apply (hasHerbrandQuotient_natCast_iff _ _).mp
  simpa only [integralIdeleClassSequence, mul_one] using hC

/-- The published integral-idele computations discharge the local input. The ordinary-unit
Herbrand formula is the only explicit premise of this helper. -/
theorem cyclicIdeleClassHerbrandQuotient_of_unitHerbrand
    (hunit : CyclicUnitHerbrandQuotient.{u,v}) :
    CyclicIdeleClassHerbrandQuotient.{u,v} := by
  apply cyclicIdeleClassHerbrandQuotient_of_integral_data hunit
    integralIdeleClassQuotientFinite integralIdeleUnitSequenceExact
  exact IntegralIdeleHerbrand.cyclicIntegralIdeleHerbrand_of
    (fun F E _ _ _ _ _ _ w => hasHerbrandQuotient_infiniteLocalRepresentation F w)

/-- The first inequality, as the Herbrand quotient identity for actual idele classes. -/
theorem cyclicIdeleClassHerbrandQuotient : CyclicIdeleClassHerbrandQuotient.{u,v} :=
  cyclicIdeleClassHerbrandQuotient_of_unitHerbrand cyclicUnitHerbrandQuotient

end Langlands.ClassField.Global
