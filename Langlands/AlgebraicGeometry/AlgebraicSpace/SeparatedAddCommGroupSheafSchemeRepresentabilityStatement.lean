import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Category.Grp.Basic

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A separated commutative group algebraic space locally of finite type over
an arbitrary field is represented by a separated scheme locally of finite type. -/
def SeparatedAddCommGroupSheafSchemeRepresentabilityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (H : FppfSheaf (Spec (CommRingCat.of k)))
    (G : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    Nonempty (G ⋙ forget AddCommGrpCat.{u + 1} ≅ H.obj) →
    IsAlgebraicSpace (Spec (CommRingCat.of k)) H →
    IsClosedImmersion (Limits.diag H.obj) →
    (∃ (U : Over (Spec (CommRingCat.of k)))
      (a : (schemeYoneda _).obj U ⟶ H.obj),
      IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom) →
    ∃ P : Over (Spec (CommRingCat.of k)),
      IsSeparated P.hom ∧ LocallyOfFiniteType P.hom ∧
        Nonempty (H.obj.RepresentableBy P)

end Langlands.AlgebraicGeometry.AlgebraicSpace
