import Langlands.ClassField.Global.IntegralIdeleUnitExactStatement
import Langlands.ClassField.Global.PrincipalIdeleUnits

/-! # Exactness of the ordinary-unit sequence in integral ideles -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField

/-- The actual unit sequence is exact by finite-place recognition of ordinary units. -/
theorem integralIdeleUnitSequenceExact : IntegralIdeleUnitSequenceExact.{u} := by
  intro E _ _
  have hprincipal : Function.Injective (IdeleGroup.unitEmbedding (𝓞 E) E) :=
    Units.map_injective (AdeleRing.algebraMap_injective (𝓞 E) E)
  constructor
  · intro a b hab
    apply Units.map_injective (IsFractionRing.injective (𝓞 E) E)
    apply hprincipal
    exact congrArg Subtype.val hab
  · ext x
    rw [integralIdelesToClasses_ker]
    change (∃ a : Eˣ, IdeleGroup.unitEmbedding (𝓞 E) E a = (x : IdeleGroup (𝓞 E) E)) ↔
      ∃ ε : (𝓞 E)ˣ, ringIntegerUnitsToIntegralIdeles E ε = x
    constructor
    · rintro ⟨a, ha⟩
      have hval : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
          Valued.v (ideleCoordinate w (IdeleGroup.unitEmbedding (𝓞 E) E a) :
            w.adicCompletion E) = 1 := by
        rw [ha]
        exact x.property
      obtain ⟨ε, hε⟩ := (principalIdeleUnitCriterion E a).mp hval
      refine ⟨ε, Subtype.ext ?_⟩
      exact (congrArg (IdeleGroup.unitEmbedding (𝓞 E) E) hε).trans ha
    · rintro ⟨ε, rfl⟩
      exact ⟨Units.map (algebraMap (𝓞 E) E).toMonoidHom ε, rfl⟩

end Langlands.ClassField.Global
