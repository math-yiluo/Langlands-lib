import Langlands.GroupScheme.Absolute.Borel

/-! # Solvability under arbitrary extension of the base field -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Solvability of a smooth affine group scheme is preserved by every extension
of its base field, expressed using an arbitrary morphism of field spectra. -/
def SolvableFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    Smooth G.X.hom → IsSolvableGroupScheme G →
      IsSolvableGroupScheme ((GroupScheme.baseChange b).obj G)

end Langlands.GroupScheme
