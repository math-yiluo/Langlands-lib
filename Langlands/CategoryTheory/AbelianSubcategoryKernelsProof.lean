import Langlands.CategoryTheory.AbelianSubcategoryStatement

/-!
# Abelian full subcategories from kernel, cokernel and finite-product closure

Proof of `Langlands.CategoryTheory.AbelianOfKernelsCokernelsFiniteProducts`,
a strengthened sufficient correction of Renard 2026, Appendix A.VI.1,
printed page 261 (PDF page 267).
-/

universe u v

open CategoryTheory

namespace Langlands.CategoryTheory

/-- Zero containment and closure under kernels, cokernels and finite products
give an abelian structure on the full subcategory, by Mathlib's instance. -/
theorem abelianOfKernelsCokernelsFiniteProducts_proof
    (C : Type u) [Category.{v} C] [Abelian C] (P : ObjectProperty C) :
    AbelianOfKernelsCokernelsFiniteProducts C P := by
  intro _ _ _ _
  exact ⟨inferInstance⟩

end Langlands.CategoryTheory
