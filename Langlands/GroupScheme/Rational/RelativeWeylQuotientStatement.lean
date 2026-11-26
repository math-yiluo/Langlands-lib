import Langlands.GroupScheme.Rational.RelativeWeylAbsoluteRestrictionStatement
import Langlands.GroupScheme.Torus.WeylPointTransport

/-! # The relative Weyl group as a quotient of a subgroup of the extended Weyl group -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The quotient-group comparison in Borel–Tits, Corollary 5.5. The subgroup of
`N(T)(K)/Z(T)(K)` represented by points normalizing both `S_K` and `T` surjects onto
`N(S)(k)/Z(S)(k)`. On simultaneous normalizer points the quotient map agrees with
restriction to `S_K` via the two point-Weyl comparisons. -/
def RelativeWeylQuotientStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G)
      (hi : IsMaximalSplitTorus i),
    let b := algebraBaseMap k K
    let iK := (GroupScheme.baseChange b).map i
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of K)))
      (j : T.toGrp ⟶ (GroupScheme.baseChange b).obj G)
      (f : (CommGroupScheme.baseChange b).obj S ⟶ T),
      IsMaximalSplitTorus j → CommGroupScheme.groupHom f ≫ j = iK →
      haveI : IsClosedImmersion iK.hom.hom.left := hi.1.2.baseChange b
      let normalizers := normalizerPoints (T := (CommGroupScheme.baseChange b).obj S) iK ⊓
        normalizerPoints j
      let toT : normalizers →* relativeWeylGroup j :=
        (QuotientGroup.mk' _).comp (Subgroup.inclusion inf_le_right)
      let toS : normalizers →*
          relativeWeylGroup (T := (CommGroupScheme.baseChange b).obj S) iK :=
        (QuotientGroup.mk' _).comp (Subgroup.inclusion inf_le_left)
      ∃ restrict : toT.range →* relativeWeylGroup i,
        Function.Surjective restrict ∧
        (relativeWeylGroupRestrict i (Over.mk b)).comp (restrict.comp toT.rangeRestrict) =
          (fibreRelativeWeylGroupEquiv b i).toMonoidHom.comp toS

end Langlands.GroupScheme
