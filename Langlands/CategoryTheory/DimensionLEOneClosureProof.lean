import Langlands.CategoryTheory.AbelianSubcategoryStatement

/-!
# Closure of the dimension-at-most-one property

Proof of `Langlands.CategoryTheory.DimensionLEOneClosedUnderSubobjectsQuotients`:
over any field, the property of being finite-dimensional of dimension at most
one contains zero and is closed under all ambient subobjects and quotients.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.CategoryTheory

/-- The dimension-at-most-one property contains zero and is closed under every
ambient monomorphism (subobject) and every ambient epimorphism (quotient). -/
theorem dimensionLEOneClosedUnderSubobjectsQuotients_proof (K : Type u) [Field K] :
    DimensionLEOneClosedUnderSubobjectsQuotients K := by
  refine ⟨⟨⟨ModuleCat.of K PUnit, ModuleCat.isZero_of_subsingleton _, ?_⟩⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact ⟨inferInstance, by rw [Module.finrank_zero_of_subsingleton]; exact zero_le_one⟩
  · intro X Y f hf hY
    obtain ⟨hYfin, hY1⟩ := hY
    have hinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp hf
    exact ⟨FiniteDimensional.of_injective f.hom hinj,
      (LinearMap.finrank_le_finrank_of_injective hinj).trans hY1⟩
  · intro X Y f hf hX
    obtain ⟨hXfin, hX1⟩ := hX
    have hsurj : Function.Surjective f.hom := (ModuleCat.epi_iff_surjective f).mp hf
    exact ⟨FiniteDimensional.of_surjective f.hom hsurj,
      (LinearMap.finrank_le_finrank_of_surjective hsurj).trans hX1⟩

end Langlands.CategoryTheory
