import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.AffineWeilRestriction
import Mathlib.FieldTheory.Separable

/-! # Split rank of an affine Weil restriction -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The rank part of Borel–Tits 6.21(i): for a finite separable field
extension `K/k` and a connected reductive group `G'` over `K`, the affine
Weil restriction of `G'` to `k` has the same split rank as `G'`. This is a
statement only. -/
def AffineWeilSplitRankStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] (G' : GroupScheme (Spec (CommRingCat.of K)))
    (hG' : IsConnectedReductive G'),
    haveI := hG'.isAffineHom
    haveI : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
    haveI := hG'.smooth
    splitRank (AffineWeil.groupScheme k K G') = splitRank G'

end Langlands.GroupScheme
