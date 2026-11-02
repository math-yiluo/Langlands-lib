import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The fppf Picard sheaf over a field as a separated algebraic space -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The actual fppf Picard class sheaf of every proper scheme over a field is an
algebraic space whose diagonal is a closed immersion, with a surjective etale
scheme atlas locally of finite type over the field. -/
def FieldPicardSheafAlgebraicSpaceStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))),
    IsProper X.hom →
      AlgebraicSpace.IsAlgebraicSpace (Spec (CommRingCat.of k))
        (RelativePicard.classSheaf X.hom) ∧
      AlgebraicSpace.IsClosedImmersion
        (Limits.diag (RelativePicard.classSheafPresheaf X.hom)) ∧
      ∃ (U : Over (Spec (CommRingCat.of k)))
        (a : (AlgebraicSpace.schemeYoneda _).obj U ⟶
          RelativePicard.classSheafPresheaf X.hom),
        AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
          LocallyOfFiniteType U.hom

end Langlands.AlgebraicGeometry.Picard
