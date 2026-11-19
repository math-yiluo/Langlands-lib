import Langlands.GroupScheme.Trigonalizable
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Trigonalizability is preserved by field extension (Milne 16.4) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.4: if an affine algebraic group `G` over a field `k` is
trigonalizable, then so is its base change `G_K` to every field `K` containing `k`. -/
def TrigonalizableBaseChangeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    IsTrigonalizable G →
      IsTrigonalizable
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

end Langlands.GroupScheme
