import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.Separable

/-! # Split unipotence descends along separable extensions (Milne 14.65) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, 14.65: an affine unipotent algebraic group `G` over a field `k` is split if it
splits over a separable algebraic field extension `K` of `k`. -/
def SeparableSplitUnipotentDescentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    IsUnipotent G →
    ∀ (K : Type u) [Field K] [Algebra k K], Algebra.IsSeparable k K →
      RelativeRoot.IsSplitUnipotent
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) →
      RelativeRoot.IsSplitUnipotent G

end Langlands.GroupScheme
