import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Yoneda

/-! # Scheme representability of the fppf Picard sheaf over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The actual fppf Picard sheaf of a proper scheme over any field is represented
by a separated scheme locally of finite type over that field. -/
def FieldPicardSheafRepresentabilityStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))),
    IsProper X.hom →
      ∃ P : Over (Spec (CommRingCat.of k)),
        IsSeparated P.hom ∧ LocallyOfFiniteType P.hom ∧
          Nonempty ((RelativePicard.classSheafPresheaf X.hom).RepresentableBy P)

end Langlands.AlgebraicGeometry.Picard
