import Langlands.GroupScheme.Reductive.Basic

/-! # Prime-to-`p` power maps on geometric points of unipotent groups are bijective
(Milne 15.2) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Lemma 15.2: let `U` be a unipotent algebraic group over a field `k` and let `e`
be an integer not divisible by the characteristic of `k`. Then `x ↦ x ^ e` is a bijection of
the group `U(k̄)` of points of `U` with values in the algebraic closure of `k`. -/
def UnipotentPowerBijectiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (U : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom],
    IsUnipotent U → ∀ e : ℤ, (e : k) ≠ 0 →
      Function.Bijective (fun x : Over.mk (toAlgebraicClosure k) ⟶ U.X => x ^ e)

end Langlands.GroupScheme
