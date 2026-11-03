import Langlands.GroupScheme.ImageGeneration
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Smooth generation by a geometrically reduced affine source -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A geometrically reduced affine finite-type source generates a smooth closed
subgroup of any affine finite-type field group. Neither connectedness of the
source nor smoothness of the ambient group is assumed. -/
def GeometricallyReducedAffineImageGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (V : Over (Spec (CommRingCat.of k))),
    IsAffineHom V.hom → LocallyOfFiniteType V.hom → GeometricallyReduced V.hom →
    ∀ f : V ⟶ G.X, ∃ E : GeneratedImage f, Smooth E.group.X.hom

end Langlands.GroupScheme
