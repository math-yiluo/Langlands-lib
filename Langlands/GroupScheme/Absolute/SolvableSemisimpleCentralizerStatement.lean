import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Rational.LeviSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Semisimple

/-! # Centralizers of semisimple points in connected solvable groups (Milne 16.40) -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Theorem 16.40: let `G` be a smooth connected affine solvable group over an
algebraically closed field `k`, and let `s` be a semisimple rational point of `G` (every
representation of `G` sends `s` to a semisimple matrix). Then every representing subgroup
`c : C ⟶ G` of the centralizer of `s` has connected underlying space, and there is a closed
unipotent subgroup `u : U ⟶ G` such that the multiplication morphism `U × C ⟶ G` is
surjective. -/
def SolvableSemisimpleCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    ∀ s : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
      (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        Module.End.IsSemisimple
          (Matrix.toLin' (ρ.rationalMatrix s : Matrix (Fin n) (Fin n) k))) →
      ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
        (G.pointCentralizer s).IsRepresentedBy c →
          ConnectedSpace C.X.left ∧
            ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G),
              IsClosedSubgroup u ∧ IsUnipotent U ∧
                Surjective (subgroupMultiplication u c).left

end Langlands.GroupScheme
