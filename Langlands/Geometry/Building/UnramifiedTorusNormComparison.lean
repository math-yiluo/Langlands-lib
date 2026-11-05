import Langlands.Geometry.Building.KPLocalNormIndependence
import Langlands.Geometry.Building.KPTorusNormIsomorphism

/-! # Torus norm comparison with arbitrary splitting fields -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E M : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) E] [IsGalois (UnramifiedClosure F) E]
  [FiniteDimensional (UnramifiedClosure F) M] [IsGalois (UnramifiedClosure F) M]
  {T U : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffine T.X.left] [IsAffine U.X.left]

/-- Isomorphic tori have compatible norm subgroups for any chosen splitting fields. -/
theorem map_torusNormIwahori_eq_of_iso_of_splitting_fields
    (e : T.toGrp ≅ U.toGrp)
    (hE : IsSplitTorus (baseChanged (UnramifiedClosure F) E T.toGrp))
    (hM : IsSplitTorus (baseChanged (UnramifiedClosure F) M U.toGrp)) :
    (torusNormIwahori (UnramifiedClosure F) E (intermediateValuation F E) T).map
        (rationalPoints.map e.hom) =
      torusNormIwahori (UnramifiedClosure F) M (intermediateValuation F M) U := by
  have hUE : IsSplitTorus (baseChanged (UnramifiedClosure F) E U.toGrp) :=
    (IsSplitTorus.iso_iff
      ((GroupScheme.baseChange (baseMap (UnramifiedClosure F) E)).mapIso e)).mp hE
  exact (map_torusNormIwahori_eq_of_iso (UnramifiedClosure F) E
    (intermediateValuation F E) e).trans
      (torusNormIwahori_eq_of_splitting_fields F E M U hUE hM)

namespace UnramifiedZeroDatum

variable {F}
  {H H' : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- An isomorphism of the chosen tori identifies their norm subgroups without
requiring the chosen splitting fields to agree. -/
theorem torusIwahori_map_eq_of_iso
    (A : UnramifiedZeroDatum F H) (B : UnramifiedZeroDatum F H')
    (e : A.T.toGrp ≅ B.T.toGrp) :
    A.torusIwahori.map (rationalPoints.map e.hom) = B.torusIwahori :=
  map_torusNormIwahori_eq_of_iso_of_splitting_fields F A.L B.L e
    A.isSplitTorus B.isSplitTorus

/-- The restriction of the actual torus point isomorphism to its norm subgroups. -/
def torusIwahoriEquivOfIso
    (A : UnramifiedZeroDatum F H) (B : UnramifiedZeroDatum F H')
    (e : A.T.toGrp ≅ B.T.toGrp) : A.torusIwahori ≃* B.torusIwahori :=
  ((isoPointsEquiv e (Over.mk (𝟙 _))).subgroupMap A.torusIwahori).trans
    (MulEquiv.subgroupCongr (A.torusIwahori_map_eq_of_iso B e))

@[simp] theorem torusIwahoriEquivOfIso_coe
    (A : UnramifiedZeroDatum F H) (B : UnramifiedZeroDatum F H')
    (e : A.T.toGrp ≅ B.T.toGrp) (t : A.torusIwahori) :
    (A.torusIwahoriEquivOfIso B e t : rationalPoints B.T.toGrp) =
      rationalPoints.map e.hom t := rfl

end UnramifiedZeroDatum

end Langlands.Geometry.Building
