import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Statement: split unipotent groups are affine spaces -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Split unipotent groups are affine spaces** (Milne, *Algebraic Groups* (2017), 14.66).
Let `H` be an affine group scheme over a field `k` admitting a subnormal series of length `n`
whose successive quotients are isomorphic to `𝔾_a` (`RelativeRoot.HasSplitSeries n H`). Then
the underlying scheme of `H` is isomorphic over `k` to the affine space `𝔸ⁿ_k`. -/
def SplitUnipotentAffineSpaceStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k))),
    IsAffineHom H.X.hom → RelativeRoot.HasSplitSeries n H →
      Nonempty (H.X ≅ Over.mk (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k)))

end Langlands.GroupScheme
