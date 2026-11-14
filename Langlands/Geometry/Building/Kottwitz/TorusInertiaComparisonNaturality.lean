import Langlands.Geometry.Building.Kottwitz.TorusInertiaFunctoriality

/-! # Naturality of the selected torus inertia comparison -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

/-- The selected torus inertia comparison commutes with actual torus morphisms
when the comparison and induced-map statements hold. -/
theorem torusInertiaComparison_natural_of_statements
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (htorus : TorusFundamentalComparisonStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hinertia : TorusInertiaComparisonStatement.{u})
    (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [IsSepClosure k E] [Normal k K] [Normal k E]
    (S T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsTorus S.toGrp) (hT : IsTorus T.toGrp) (f : S ⟶ T)
    (x : FundamentalInertia k K E S.toGrp hS.isConnectedReductive_of_fieldSplitting) :
    torusInertiaComparison k K E T hT
        (fundamentalInertiaMap k K E T.toGrp hT.isConnectedReductive_of_fieldSplitting
          S.toGrp hS.isConnectedReductive_of_fieldSplitting (CommGroupScheme.groupHom f) x) =
      torusInertiaMap k E f K (torusInertiaComparison k K E S hS x) := by
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective
    ((fundamentalGroupGalois k S.toGrp E hS.isConnectedReductive_of_fieldSplitting).comp
      (relativeInertia k K E).subtype) x
  change torusInertiaComparison k K E T hT
      (fundamentalInertiaMap k K E T.toGrp hT.isConnectedReductive_of_fieldSplitting
        S.toGrp hS.isConnectedReductive_of_fieldSplitting (CommGroupScheme.groupHom f)
        (fundamentalInertiaProjection k K E S.toGrp
          hS.isConnectedReductive_of_fieldSplitting y)) = _
  rw [((hmap k K E).1 S.toGrp T.toGrp hS.isConnectedReductive_of_fieldSplitting
    hT.isConnectedReductive_of_fieldSplitting (CommGroupScheme.groupHom f)).2.1,
    (hinertia k K E T hT).2.1, (hinertia k K E S hS).2.1,
    torusInertiaMap_projection,
    torusFundamentalComparison_natural_of_statements k E f hcmp hfund htorus]

end Langlands.Geometry.Building.Kottwitz
