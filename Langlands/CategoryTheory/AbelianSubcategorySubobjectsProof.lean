import Langlands.CategoryTheory.AbelianSubcategoryStatement

/-!
# Abelian full subcategories from subobject, quotient and finite-product closure

Proof of `Langlands.CategoryTheory.AbelianOfSubobjectsQuotientsFiniteProducts`,
a strengthened sufficient correction of Renard 2026, Appendix A.VI.1,
printed page 261 (PDF page 267).
-/

universe u v

open CategoryTheory

namespace Langlands.CategoryTheory

/-- Zero containment and closure under all ambient subobjects, quotients and
finite products give an abelian structure on the full subcategory. Subobject
closure yields kernel closure and quotient closure yields cokernel closure. -/
theorem abelianOfSubobjectsQuotientsFiniteProducts_proof
    (C : Type u) [Category.{v} C] [Abelian C] (P : ObjectProperty C) :
    AbelianOfSubobjectsQuotientsFiniteProducts C P := by
  intro _ _ _ _
  have : P.IsClosedUnderKernels := inferInstance
  have : P.IsClosedUnderCokernels := inferInstance
  exact ⟨inferInstance⟩

end Langlands.CategoryTheory
