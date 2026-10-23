import Langlands.ClassField.Global.IdeleCohomologyExactnessStatement
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # Exactness of the principal-idele cohomology sequence -/

namespace Langlands.ClassField.Global

universe u

/-- The short exact coefficient sequence gives exactness in every natural degree. -/
theorem ideleCohomologyExactness : IdeleCohomologyExactness.{u} := by
  intro F E _ _ _ _ n
  exact (groupCohomology.mapShortComplex₂_exact
    (ideleCoefficientSequence_shortExact F E) n).moduleCat_range_eq_ker

variable (F E : Type u) [Field F] [Field E] [NumberField E] [Algebra F E]

/-- A class maps to zero in idele-class cohomology precisely when it is principal. -/
theorem ideleQuotientCohomologyMap_eq_zero_iff (n : ℕ)
    (x : relativeIdeleCohomology F E n) :
    ideleQuotientCohomologyMap F E n x = 0 ↔
      ∃ y, principalIdeleCohomologyMap F E n y = x := by
  change x ∈ LinearMap.ker (ideleQuotientCohomologyMap F E n).hom ↔
    x ∈ LinearMap.range (principalIdeleCohomologyMap F E n).hom
  rw [ideleCohomologyExactness F E n]

end Langlands.ClassField.Global
