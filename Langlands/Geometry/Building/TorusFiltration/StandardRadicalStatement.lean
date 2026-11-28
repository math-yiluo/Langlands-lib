import Langlands.Geometry.Building.TorusFiltration.ConnectedNeronModel
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # The pro-unipotent radical of the standard torus filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- KP Proposition B.9.1 over the maximal unramified field: the preimage, under
reduction of integral sections of the connected Néron model, of the rational
points of a represented unipotent radical of its special fibre, mapped into
`T(K)`, is the intersection of `T(K)^0` with the strict-depth union at zero of
the standard filtration. -/
def StandardTorusZeroPlusRadicalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] (hT : IsTorus T.toGrp),
    let M := connectedNeronModel F T hT
    ∃ (U : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))))
      (i : U ⟶ M.specialFibre), IsUnipotentRadical i ∧
        (↑(((rationalPoints.map i).range.comap M.reduction).map M.integralPointMap) :
            Set (rationalPoints T.toGrp)) =
          (M.integralPoints : Set (rationalPoints T.toGrp)) ∩
            (⋃ r : Set.Ioi (0 : ℝ≥0),
              (localTorusFiltration F T hT r : Set (rationalPoints T.toGrp)))

end Langlands.Geometry.Building
