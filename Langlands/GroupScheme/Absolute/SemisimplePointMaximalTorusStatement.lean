import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Semisimple

/-! # Semisimple points lie in maximal tori (Milne 17.36) -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 17.36: let `G` be a smooth connected affine group over an
algebraically closed field `k`, and let `s` be a semisimple rational point of `G` (every
representation of `G` sends `s` to a semisimple matrix). Then `s` factors through a maximal
torus `j : T ⟶ G`. -/
def SemisimplePointMaximalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (s : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X),
    (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
      Module.End.IsSemisimple
        (Matrix.toLin' (ρ.rationalMatrix s : Matrix (Fin n) (Fin n) k))) →
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
      (t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ T.toGrp.X),
      IsMaximalTorus j ∧ t ≫ j.hom.hom = s

end Langlands.GroupScheme
