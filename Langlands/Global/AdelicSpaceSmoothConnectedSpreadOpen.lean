import Langlands.Global.AdelicSpaceSmoothConnectedAdelicOpen
import Langlands.Global.AdelicSpaceSmoothModelGeometry
import Langlands.Global.AdelicSpaceSpreadMapStatement

/-! # Smooth adelic openness for arbitrary supplied models -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- The exact space Lang–Weil estimate suffices for Conrad's Theorem 5.9,
with the original arbitrary supplied models and their actual adelic topologies. -/
def AdelicSpaceSpreadSmoothOpenOfLangWeilStatement : Prop :=
  SpaceUniformLangWeilStatement.{u} → AdelicSpaceSpreadSmoothOpenStatement.{u}

/-- Transport the smooth connected model theorem to arbitrary supplied models.
The exact uniform Lang–Weil estimate remains a premise. -/
theorem adelicSpaceSpreadSmoothOpen_of_langWeil :
    AdelicSpaceSpreadSmoothOpenOfLangWeilStatement.{u} := by
  intro hLW
  constructor
  · intro k F _ _ _ _ _ _ _ S U hS hU X Z hX hftX hZ hftZ Y W e f g hg _ hgc
    obtain ⟨T, M, N, hT, hM, hftM, hN, hftN, eT, fT, gm, hgm, hconn, w⟩ :=
      AdelicSpaceSmoothModelGeometry.curvePlaceSpaceSmoothConnectedModel
        k F S U hS hU X Z hX hftX hZ hftZ Y W e f g hg hgc
    have hopen := curvePlaceSmoothConnectedAdele_isOpenMap
      k F T hLW hT hM hftM hN hftN gm hgm hconn
    have hspread := curvePlaceSpaceSpread_isOpenMap_of_model
      k F T Y W eT fT gm g hopen w
    rw [(adelicSpacePointTopology.1.2.2.2 k F).2
        S T hS hT X M hX hftX hM hftM Y e eT,
      (adelicSpacePointTopology.1.2.2.2 k F).2
        U T hU hT Z N hZ hftZ hN hftN W f fT]
    exact hspread
  · intro K _ _ S U X Z hX hftX hZ hftZ Y W e f g hg _ hgc
    obtain ⟨T, M, N, hM, hftM, hN, hftN, eT, fT, gm, hgm, hconn, w⟩ :=
      AdelicSpaceSmoothModelGeometry.numberFieldSpaceSmoothConnectedModel
        K S U X Z hX hftX hZ hftZ Y W e f g hg hgc
    have hopen := numberFieldSmoothConnectedAdele_isOpenMap
      K T hLW hM hftM hN hftN gm hgm hconn
    have hspread := numberFieldSpaceSpread_isOpenMap_of_model
      K T Y W eT fT gm g hopen w
    rw [(adelicSpacePointTopology.2.2.2.2 K).2
        S T X M hX hftX hM hftM Y e eT,
      (adelicSpacePointTopology.2.2.2.2 K).2
        U T Z N hZ hftZ hN hftN W f fT]
    exact hspread

end Langlands.Global
