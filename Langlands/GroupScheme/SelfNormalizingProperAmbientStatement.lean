import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an affine base, a smooth self-normalizing closed connected subgroup
admits an exact-coset map into a proper scheme of finite presentation. -/
def SelfNormalizingProperAmbientStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (i : H ⟶ G),
    GeometricallyConnected G.X.hom → IsClosedSubgroup i →
    Smooth H.X.hom → GeometricallyConnected H.X.hom →
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i →
    ∃ (Y : Over (Spec (CommRingCat.of R))) (r : G.X ⟶ Y),
      IsProper Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ G.X),
        g ≫ r = h ≫ r ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T

end Langlands.GroupScheme
