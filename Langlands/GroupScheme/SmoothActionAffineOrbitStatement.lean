import Langlands.GroupScheme.SchemeActionOrbit
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine orbits of a smooth action relation -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme.SchemeAction

/-- If the action relation of a smooth affine group on an affine finite-type
scheme is smooth, each rational orbit is an affine clopen subscheme with a
smooth surjective quasi-compact orbit projection. -/
def SmoothActionAffineOrbitStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (X : Over (Spec (CommRingCat.of k)))
    [IsAffineHom X.hom] [LocallyOfFiniteType X.hom]
    (a : SchemeAction G X),
      Smooth (lift a.hom (snd G.X X)).left →
      ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X),
        ∃ (Q : Over (Spec (CommRingCat.of k)))
          (q : G.X ⟶ Q) (j : Q ⟶ X),
          IsAffineHom Q.hom ∧ LocallyOfFiniteType Q.hom ∧
          QuasiCompact Q.hom ∧ IsOpenImmersion j.left ∧
          IsClosedImmersion j.left ∧ Smooth q.left ∧
          Surjective q.left ∧ QuasiCompact q.left ∧
          q ≫ j = a.orbitMap x

end Langlands.GroupScheme.SchemeAction
