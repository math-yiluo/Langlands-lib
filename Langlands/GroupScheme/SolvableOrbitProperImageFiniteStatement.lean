import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.SchemeAction
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper images in homogeneous spaces of solvable groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every proper scheme has finite image in a reduced separated finite-type
scheme on whose rational points a smooth connected affine solvable group acts
transitively. -/
def SolvableOrbitProperImageFiniteStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left → IsSolvableGroupScheme G →
      ∀ (O : Over (Spec (CommRingCat.of k))),
        IsReduced O.left → IsSeparated O.hom →
          LocallyOfFiniteType O.hom → QuasiCompact O.hom →
            ∀ (a : SchemeAction G O)
              (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O),
              (∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O,
                ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
                  a.act g x = y) →
                ∀ (Z : Over (Spec (CommRingCat.of k))),
                  IsProper Z.hom → ∀ (j : Z ⟶ O), (Set.range j.left).Finite

end Langlands.GroupScheme
