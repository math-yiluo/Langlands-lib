import Langlands.GroupScheme.RelativeLevi.FaceCoverQuotientCharts
import Langlands.GroupScheme.RelativeUnipotent.LiftedScalarLocality

/-! # Recovery of the original global quotient on each actual chart component -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open RelativeUnipotent RelativeUnipotent.NaturalModuleTransformations

variable {S : Scheme.{u}} [IsAffine S] {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

/-- The actual cover module with its original independent finite-free pieces. -/
def layerBundlePresentation (d : ℕ) : DisjointFreePresentation (D.layerBundle d) where
  cover := D.groupsOpenCover
  disjoint := D.groupsOpenCover_isDisjoint
  rank := D.layerRank d
  pieceIso := D.layerBundlePieceIso d

/-- The original global quotient on one original affine chart is its actual
original vector quotient, through the prescribed cover comparison. -/
def globalFaceQuotientComponentIso (d : ℕ) (i : D.Index) :
    (baseChange (D.charts i.down).2.projection).obj
        (D.globalFaceQuotientData r hG hp hr d).group ≅
      (D.charts i.down).2.layerGroup d :=
  (Descent.pullbackComparison D.groupsBaseMap (D.componentMap i)
      (D.charts i.down).2.projection (D.componentMap_comp_groupsBaseMap i)
      (D.globalFaceQuotientData r hG hp hr d).group).symm ≪≫
    (baseChange (D.componentMap i)).mapIso
      (D.globalFaceQuotientData r hG hp hr d).coverIso ≪≫ D.layerComponentIso d i

/-- Component recovery retains the original global projection and the original
local quotient projection, through the actual original term comparison. -/
lemma globalFaceQuotientComponentIso_projection (d : ℕ) (i : D.Index) :
    (baseChange (D.charts i.down).2.projection).map
        (D.globalFaceQuotientData r hG hp hr d).projection ≫
        (D.globalFaceQuotientComponentIso r hG hp hr d i).hom =
      (D.globalTermChartIso r hG hp hr d i).hom ≫ (D.charts i.down).2.layerProjection d := by
  let eK := Descent.pullbackComparison D.groupsBaseMap (D.componentMap i)
    (D.charts i.down).2.projection (D.componentMap_comp_groupsBaseMap i)
    (D.globalTerm r hG hp hr d)
  let eQ := Descent.pullbackComparison D.groupsBaseMap (D.componentMap i)
    (D.charts i.down).2.projection (D.componentMap_comp_groupsBaseMap i)
    (D.globalFaceQuotientData r hG hp hr d).group
  apply (cancel_epi eK.hom).mp
  change eK.hom ≫ (baseChange (D.charts i.down).2.projection).map
      (D.globalFaceQuotientData r hG hp hr d).projection ≫
        eQ.inv ≫ (baseChange (D.componentMap i)).map
          (D.globalFaceQuotientData r hG hp hr d).coverIso.hom ≫
            (D.layerComponentIso d i).hom = _
  rw [← Category.assoc eK.hom, ← Descent.pullbackComparison_naturality]
  dsimp only [eQ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, (D.globalFaceQuotientData r hG hp hr d).recovery,
    coverProjection, Functor.map_comp, Category.assoc, D.layerProjection_component,
    ← Category.assoc, D.globalTermCoverIso_component]
  simp only [Category.assoc, eK]

/-- The actual global quotient has the exact vector-bundle additive structure
as soon as the original affine component point scalar comparison is proved. -/
lemma isVectorBundleAdditive_globalFaceQuotient_of_specComponents (d : ℕ)
    (h : (D.globalFaceQuotientCharts r hG hp hr d).SpecComponentIndependent D.groupsOpenCover) :
    IsVectorBundleAdditive (D.globalFaceQuotientData r hG hp hr d).group := by
  let : IsAffineHom (D.globalFaceQuotientData r hG hp hr d).group.X.hom :=
    D.globalFaceQuotient_isAffineHom r hG hp hr d
  let : Smooth (D.globalFaceQuotientData r hG hp hr d).group.X.hom :=
    D.globalFaceQuotient_smooth r hG hp hr d
  exact (D.globalFaceQuotientCharts r hG hp hr d).isVectorBundleAdditive_of_linearTransitions
    (D.layerBundlePresentation d)
    ((D.globalFaceQuotientCharts r hG hp hr d).hasLinearTransitions_of_scalarIndependent
      ((D.globalFaceQuotientCharts r hG hp hr d).scalarIndependent_of_specComponents
        D.groupsOpenCover h))
    (D.layerBundle_isFiniteLocallyFree d)

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
