import Langlands.ClassField.Global.PrincipalIdeleUnitStatement

/-! # Recognizing ordinary units among principal ideles -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

variable {E : Type u} [Field E] [NumberField E]

private theorem principalCompletionValuation (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := by
  simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply] using (valuedAdicCompletion_eq_valuation' (v := w) x)

/-- Finite-place unit recognition for the actual principal idele. -/
theorem principalIdeleUnitCriterion : PrincipalIdeleUnitCriterion.{u} := by
  intro E _ _ a
  constructor
  · intro h
    have hv (w : HeightOneSpectrum (𝓞 E)) : w.valuation E (a : E) = 1 := by
      rw [← principalCompletionValuation, ← ideleCoordinate_unitEmbedding]
      exact h w
    obtain ⟨x, hx⟩ := mem_integers_of_valuation_le_one E (a : E) (fun w => (hv w).le)
    obtain ⟨y, hy⟩ := mem_integers_of_valuation_le_one E ((a : E)⁻¹) (by
      intro w
      rw [map_inv₀, hv w, inv_one])
    have hxy : x * y = 1 := RingOfIntegers.coe_injective (by
      rw [map_mul, hx, hy, map_one, mul_inv_cancel₀ (Units.ne_zero a)])
    refine ⟨⟨x, y, hxy, by simpa only [mul_comm] using hxy⟩, ?_⟩
    exact Units.ext hx
  · rintro ⟨ε, rfl⟩ w
    rw [ideleCoordinate_unitEmbedding, principalCompletionValuation]
    change w.valuation E (algebraMap (𝓞 E) E (ε : 𝓞 E)) = 1
    exact Valuation.Integers.one_of_isUnit' ε.isUnit (w.valuation_le_one (K := E))

end Langlands.ClassField.Global
