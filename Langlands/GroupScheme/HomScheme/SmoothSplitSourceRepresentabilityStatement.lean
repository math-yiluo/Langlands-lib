import Langlands.GroupScheme.HomScheme.Universal
import Langlands.GroupScheme.Torus.Split

/-! # Smooth representability of Hom from a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomScheme

/-- The actual relative Hom presheaf from a split torus to a smooth affine
group scheme is represented by a smooth scheme over the original base. -/
def SmoothSplitSourceRepresentabilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    IsSplitTorus H →
    ∃ (M : Over S) (i : RelativeHom H G M),
      IsUniversal i ∧ Smooth M.hom

end Langlands.GroupScheme.HomScheme
