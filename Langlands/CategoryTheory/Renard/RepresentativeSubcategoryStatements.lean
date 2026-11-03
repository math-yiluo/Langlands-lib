import Langlands.CategoryTheory.Renard.RepresentativeSubcategory

/-!
# Renard A.II.2: equivalence with the full representative subcategory

The conclusion is a quasi-inverse of the actual full-subcategory inclusion,
with both actual natural isomorphisms. This module only states the comparison.
-/

universe v u

open CategoryTheory

namespace Langlands.Renard

/-- Renard's representative-subcategory comparison, A.II.2, printed
pp.250–251 / PDF256–257. The full subcategory of selected representatives
has an actual quasi-inverse to its inclusion in the ambient category. -/
@[pp_with_univ]
def RepresentativeSubcategoryEquivalenceStatement
    (C : Type u) [Category.{v} C] : Prop :=
  ∃ G : C ⥤ RepresentativeSubcategory C,
    Nonempty (representativeInclusion C ⋙ G ≅ 𝟭 (RepresentativeSubcategory C)) ∧
    Nonempty (G ⋙ representativeInclusion C ≅ 𝟭 C)

end Langlands.Renard
