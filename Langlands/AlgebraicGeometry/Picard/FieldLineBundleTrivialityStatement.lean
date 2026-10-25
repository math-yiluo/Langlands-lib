import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # Triviality of line bundles on the spectrum of a field -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Every actual locally free rank-one module sheaf on a field spectrum is
isomorphic to the structure sheaf. This declaration states the proposition. -/
def FieldLineBundleTrivialityStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (L : LineBundle (Spec (CommRingCat.of K))),
    Nonempty (L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (Spec (CommRingCat.of K)))

end Langlands.AlgebraicGeometry.Picard
