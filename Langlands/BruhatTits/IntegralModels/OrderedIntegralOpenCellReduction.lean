import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellProof

/-! # Reduction of the ordered integral open cell to two torus inputs -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- The connected-model bound and the connected-image description of the torus
Iwahori subgroup together imply the ordered integral open-cell existence target. -/
def UnramifiedOrderedIntegralOpenCellReductionStatement : Prop :=
  UnramifiedTorusConnectedBoundStatement.{u} →
  UnramifiedTorusIwahoriConnectedImageStatement.{u} →
  UnramifiedOrderedIntegralOpenCellStatement.{u}

open OrderedIntegralOpenCell in
/-- Proof of the reduction. The family consists of the root models of an actual
closed integral split torus of `N` and the relative identity component of its integral
centralizer; the two torus inputs identify the integral points of the latter with the
torus Iwahori subgroup. -/
theorem unramifiedOrderedIntegralOpenCellReduction :
    UnramifiedOrderedIntegralOpenCellReductionStatement.{u} := by
  intro hConn hImg F _ _ _ _ G _ C E hrep x Ω hne hb N hN hpts
  have : Smooth N.group.X.hom := hN
  have : GeometricallyConnected E.T.toGrp.X.hom :=
    geometricallyConnected_of_isSplitTorus_baseChanged E.T.toGrp E.isSplitTorus
  obtain ⟨T, -⟩ := exists_integralSplitTorusData C E Ω N hpts
  obtain ⟨H, iH, hiH, hH, hgc⟩ := RelativeIdentityComponent.smoothExistence _
    (T.centralizerModel E.i hrep).group (T.centralizerModel_isSmooth E.i hrep)
  have htor := neutralCentralizer_integralPoints_eq hrep hConn hImg hpts T hiH hH hgc
  refine ⟨family hrep hpts hne hb T x hiH hH hgc htor, ?_⟩
  intro ν hν nneg npos aneg apos hinjN hrN hinjP hrP
  exact isOpenImmersion_family hpts T hrep hne hb x hiH hH hgc htor ν hν aneg apos
    hinjN hrN hinjP hrP

end Langlands.BruhatTits.IntegralModels
