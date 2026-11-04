import Langlands.GroupScheme.MatrixRepresentationConjugate
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

/-- Rational-point triangularization of every actual representation. -/
def LieKolchinRationalTriangularizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) →
      ∀ (N : ℕ) (ρ : MatrixRepresentation H (Fin N)),
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
            (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X,
          ∀ (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
            (i j : Fin N), j < i →
              (ρ.conjugate g).pointMatrix
                (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x i j = 0

end Langlands.GroupScheme
