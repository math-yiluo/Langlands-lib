import Langlands.ClassField.Global.IntegralIdeleClassQuotientFiniteStatement
import Langlands.ClassField.Global.FiniteDivisorFractionalIdeal
import Langlands.ClassField.Global.PrincipalIdeleDivisor
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! # Finiteness of the actual residual idele-class quotient -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField nonZeroDivisors

variable (E : Type u) [Field E] [NumberField E]

private def ideleFractionalIdeal : IdeleGroup (𝓞 E) E →*
    (FractionalIdeal (𝓞 E)⁰ E)ˣ :=
  (finiteDivisorFractionalIdealEquiv E).toMonoidHom.comp (ideleDivisorHom E)

private theorem ideleFractionalIdeal_principal (a : Eˣ) :
    ideleFractionalIdeal E (IdeleGroup.unitEmbedding (𝓞 E) E a) =
      toPrincipalIdeal (𝓞 E) E a := by
  apply fractionalIdealDivisor_injective E
  change fractionalIdealDivisor E
    (finiteDivisorFractionalIdeal E (ideleDivisor (IdeleGroup.unitEmbedding (𝓞 E) E a))) = _
  rw [fractionalIdealDivisor_finiteDivisorFractionalIdeal]
  ext w
  simpa only [ideleDivisor_apply, fractionalIdealDivisor_apply, coe_toPrincipalIdeal]
    using principalIdeleDivisorFormula E w a

private theorem ideleFractionalIdeal_eq_one_iff (x : IdeleGroup (𝓞 E) E) :
    ideleFractionalIdeal E x = 1 ↔ x ∈ integralIdeles E := by
  change finiteDivisorFractionalIdeal E (ideleDivisor x) = 1 ↔ _
  rw [← finiteDivisorFractionalIdeal_zero E]
  have hi : Function.Injective (finiteDivisorFractionalIdeal E) := by
    intro d e h
    simpa only [fractionalIdealDivisor_finiteDivisorFractionalIdeal] using
      congrArg (fractionalIdealDivisor E) h
  rw [hi.eq_iff, ideleDivisor_eq_zero_iff]
  rfl

private abbrev FractionalIdealClass :=
  (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range

private def ideleIdealClass : IdeleGroup (𝓞 E) E →* FractionalIdealClass E :=
  (QuotientGroup.mk' (toPrincipalIdeal (𝓞 E) E).range).comp (ideleFractionalIdeal E)

private theorem principal_le_ideleIdealClass_ker :
    IdeleGroup.principalSubgroup (𝓞 E) E ≤ (ideleIdealClass E).ker := by
  rintro x ⟨a, rfl⟩
  change QuotientGroup.mk (ideleFractionalIdeal E
    (IdeleGroup.unitEmbedding (𝓞 E) E a)) = (1 : FractionalIdealClass E)
  rw [ideleFractionalIdeal_principal, QuotientGroup.eq_one_iff]
  exact ⟨a, rfl⟩

private def ideleClassIdealClass : IdeleClassGroup (𝓞 E) E →* FractionalIdealClass E :=
  QuotientGroup.lift _ (ideleIdealClass E) (principal_le_ideleIdealClass_ker E)

private theorem ideleClassIdealClass_ker :
    (ideleClassIdealClass E).ker = integralIdeleClasses E := by
  ext c
  refine QuotientGroup.induction_on c fun x => ?_
  change ideleIdealClass E x = 1 ↔
    ∃ y ∈ integralIdeles E,
      (QuotientGroup.mk y : IdeleClassGroup (𝓞 E) E) = QuotientGroup.mk x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff (ideleFractionalIdeal E x)).mp hx
    let p := IdeleGroup.unitEmbedding (𝓞 E) E a
    have hp : QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E) p = 1 :=
      (QuotientGroup.eq_one_iff p).mpr ⟨a, rfl⟩
    refine ⟨x / p, (ideleFractionalIdeal_eq_one_iff E _).mp ?_, ?_⟩
    · rw [map_div, show ideleFractionalIdeal E p = toPrincipalIdeal (𝓞 E) E a from
        ideleFractionalIdeal_principal E a, ha, div_self']
    · change (QuotientGroup.mk' _ (x / p)) = QuotientGroup.mk' _ x
      rw [map_div, hp, div_one]
  · rintro ⟨y, hy, hxy⟩
    have hy' : ideleIdealClass E y = 1 := by
      change QuotientGroup.mk (ideleFractionalIdeal E y) = (1 : FractionalIdealClass E)
      rw [(ideleFractionalIdeal_eq_one_iff E y).mpr hy]
      rfl
    have h := congrArg (ideleClassIdealClass E) hxy
    exact h.symm.trans hy'

/-- Finiteness follows by embedding the residual quotient in the finite ideal class group. -/
theorem integralIdeleClassQuotientFinite : IntegralIdeleClassQuotientFinite.{u} := by
  intro E _ _
  let : Finite (FractionalIdealClass E) :=
    Finite.of_equiv (ClassGroup (𝓞 E)) (ClassGroup.equiv E).toEquiv
  let f : IntegralIdeleClassQuotient E →* FractionalIdealClass E :=
    QuotientGroup.lift _ (ideleClassIdealClass E) (ideleClassIdealClass_ker E).ge
  have hf : Function.Injective f :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr (ideleClassIdealClass_ker E).symm
  exact Finite.of_injective f hf

end Langlands.ClassField.Global
