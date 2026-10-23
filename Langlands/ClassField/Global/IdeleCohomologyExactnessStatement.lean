import Langlands.ClassField.Global.IdeleCoefficientSequence

/-! # Image–kernel exactness for principal-idele cohomology -/

namespace Langlands.ClassField.Global

universe u

/-- The image of principal cohomology is the kernel of the idele-class quotient map. -/
def IdeleCohomologyExactness : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    LinearMap.range (principalIdeleCohomologyMap F E n).hom =
      LinearMap.ker (ideleQuotientCohomologyMap F E n).hom

end Langlands.ClassField.Global
