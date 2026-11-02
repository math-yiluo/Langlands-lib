import Langlands.CategoryTheory.DimensionLEOneNoProductProof

/-!
# The dimension-at-most-one subcategory is not abelian

Proof of `Langlands.CategoryTheory.DimensionLEOneNotAbelian`: an abelian
structure would supply finite products, hence a binary product of the actual
line with itself, which does not exist.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.CategoryTheory

/-- The full subcategory of vector spaces of dimension at most one admits no
abelian structure. -/
theorem dimensionLEOneNotAbelian_proof (K : Type u) [Field K] :
    DimensionLEOneNotAbelian K := by
  rintro ⟨hab⟩
  exact dimensionLEOneLineHasNoBinaryProduct_proof K inferInstance

end Langlands.CategoryTheory
