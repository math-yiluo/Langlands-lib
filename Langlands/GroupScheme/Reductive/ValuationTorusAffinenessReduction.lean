import Langlands.GroupScheme.Reductive.EtaleTorusAffinenessReduction
import Langlands.GroupScheme.Torus.ValuationSelfCentralizingWeyl
import Langlands.AlgebraicGeometry.AlgClosedValuationEtaleAffineness

/-! # Fibrewise affineness from torus families and the Weyl criterion -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The proved valuation affineness theorem removes the valuation hypothesis
from the arbitrary-base finite Weyl model construction. -/
def SelfCentralizingWeyl.finiteWeylModelOfCriterion
    (hcrit : SelfCentralizingTorusWeylAffinenessStatement.{u})
    (S : Scheme.{u}) (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasConnectedReductiveResidueFibers G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hself : (torusCentralizer t).IsRepresentedBy t) :
    SelfCentralizingWeyl.FiniteWeylModel t := by
  apply SelfCentralizingWeyl.valuationFiniteWeylModel hcrit
    (S := S) (G := G) (hG := hG) (T := T) (t := t)
    (hT := hT) (ht := ht) (hmax := hmax) (hself := hself)
  intro K _ _ A X f hqc hsep het
  let : QuasiCompact f := hqc
  let : IsSeparated f := hsep
  let : Etale f := het
  exact Langlands.AlgebraicGeometry.isAffineHom_etale_algClosedValuation K A f

/-- The exact arbitrary-base target follows from universal torus-family
existence and the structural Weyl-affineness criterion. The valuation
affineness needed for this reduction is proved, rather than assumed. -/
theorem reductiveFiberAffineness_of_torusFamilies_of_weylCriterion
    (hfamilies : ∀ (S : Scheme.{u}) (G : GroupScheme S)
      [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
      (∀ s : S, IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
      ∃ (M : Over S) (K : GroupScheme M.left)
        (j : K ⟶ (baseChange M.hom).obj G),
        IsClosedSubgroup j ∧ RelativeTorus.IsTorus K ∧
          TorusSubgroupModuli.IsUniversal j ∧ Smooth M.hom)
    (hcrit : SelfCentralizingTorusWeylAffinenessStatement.{u}) :
    ReductiveFiberAffinenessStatement.{u} := by
  apply reductiveFiberAffineness_of_torusFamilies_of_selfCentralizing hfamilies
  intro S G _ _ _ hG T t hT ht hmax hself
  exact (SelfCentralizingWeyl.finiteWeylModelOfCriterion hcrit
    S G hG T t hT ht hmax hself).group_affine

end Langlands.GroupScheme
