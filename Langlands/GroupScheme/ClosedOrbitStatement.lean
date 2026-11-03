import Langlands.GroupScheme.SchemeAction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Existence of a closed orbit with its reduced structure -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth affine group acting on a nonempty scheme of finite type over an algebraically
closed field has a closed orbit: a reduced closed subscheme `O` of finite type, stable under the
action, whose rational points form a single orbit of the rational points of the group. -/
def ClosedOrbitStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    Nonempty X.left → ∀ a : SchemeAction G X,
      ∃ (O : Over (Spec (CommRingCat.of k))) (j : O ⟶ X) (b : SchemeAction G O)
        (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O),
        IsReduced O.left ∧ IsClosedImmersion j.left ∧ LocallyOfFiniteType O.hom ∧
          QuasiCompact O.hom ∧
          (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (o : T ⟶ O),
            b.act g o ≫ j = a.act g (o ≫ j)) ∧
          ∀ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O,
            ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X, b.act g x = y

end Langlands.GroupScheme
