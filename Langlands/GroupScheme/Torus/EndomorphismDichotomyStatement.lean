import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Statement: surjectivity or a closed multiplicative subgroup in a torus kernel -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

universe u

/-- Over an algebraically closed field, an actual torus endomorphism is surjective on
underlying schemes or annihilates an actual closed copy of `Gm`. This is a derived
generalization of the torus-kernel step in Milne's proof of Theorem 17.48. -/
def TorusEndomorphismDichotomyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
    ∀ f : T ⟶ T,
      Surjective (CommGroupScheme.groupHom f).hom.hom.left ∨
        ∃ ν : Gm (Spec (CommRingCat.of k)) ⟶ T,
          IsClosedSubgroup (CommGroupScheme.groupHom ν) ∧ ν ≫ f = 0

end Langlands.GroupScheme
