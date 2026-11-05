import Langlands.Geometry.Building.KPZeroProductOpenness
import Langlands.Geometry.Building.KPUnramifiedNormedTopology
import Langlands.Geometry.Building.KPCharacterKernelTopology
import Langlands.Geometry.Building.KPZeroTopologyDescent
import Langlands.Geometry.Building.KPCentralizerZeroCompactOpenStatement
import Langlands.GroupScheme.AffineWeilRestrictionForwardTopology
import Langlands.GroupScheme.Torus.GaloisNormRational
import Langlands.GroupScheme.Torus.GaloisNormSmoothness
import Langlands.GroupScheme.SimplyConnected.DerivedCoverTorusProductSmoothStatement
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothOpenMapProof

/-! # Openness of the actual zero subgroups from the two smoothness statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology CategoryTheory.MonoidalCategory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  (E : UnramifiedZeroDatum F H)

/-- The split base change `T_L` is affine. -/
theorem isAffine_splitTorus :
    IsAffine (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp).X.left := by
  have : IsAffineHom (GaloisPointComparison.baseChanged
      (UnramifiedClosure F) E.L E.T.toGrp).X.hom := E.isSplitTorus.isAffineHom
  exact isAffine_of_isAffineHom (GaloisPointComparison.baseChanged
    (UnramifiedClosure F) E.L E.T.toGrp).X.hom

/-- The split base change `T_L` is locally of finite type. -/
theorem locallyOfFiniteType_splitTorus :
    LocallyOfFiniteType
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp).X.hom := by
  have := E.isSplitTorus.smooth
  infer_instance

/-- The splitting field is a free module over `K`. -/
theorem moduleFree_splittingField : Module.Free (UnramifiedClosure F) E.L :=
  Module.Free.of_divisionRing (UnramifiedClosure F) E.L

/-- The splitting field is a projective module over `K`. -/
theorem moduleProjective_splittingField : Module.Projective (UnramifiedClosure F) E.L :=
  @Module.Projective.of_free _ _ _ _ _ E.moduleFree_splittingField

-- Generic instance search for these two classes on `E.L` times out.
attribute [local instance] moduleFree_splittingField moduleProjective_splittingField

section Weil

variable
  [IsAffine (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp).X.left]
  [LocallyOfFiniteType
    (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp).X.hom]

/-- The bounded subgroup `T(L)^b` transported to `K`-points of the Weil restriction
`R_{L/K}(T_L)` by the published rational-point identification. -/
def weilKernel : Subgroup (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E.L
    (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp))) :=
  (characterValuationKernel (intermediateValuation F E.L)
    (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)).map
      (GaloisNorm.rationalPointsEquiv (UnramifiedClosure F) E.L E.T).toMonoidHom

/-- `T(K)^0` is the image of `weilKernel` under the algebraic norm. -/
theorem torusIwahori_eq_map_weilKernel :
    E.torusIwahori = E.weilKernel.map
      (rationalPoints.map (GaloisNorm.norm (UnramifiedClosure F) E.L E.T)) := by
  rw [weilKernel, Subgroup.map_map]
  change Subgroup.map (GaloisPointComparison.rationalNorm (UnramifiedClosure F) E.L E.T) _ = _
  congr 1
  refine MonoidHom.ext fun x => ?_
  exact (GaloisNorm.norm_rationalPoints (UnramifiedClosure F) E.L E.T x).symm

/-- The inverse of `rationalPointsEquiv`, written as the explicit coefficient composite. -/
theorem rationalPointsEquiv_symm_eq :
    ((GaloisNorm.rationalPointsEquiv (UnramifiedClosure F) E.L E.T).symm :
      rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E.L
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)) →
      rationalPoints (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)) =
      fun x => (GaloisPointComparison.rationalCoeffEquiv E.L
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)).symm
        (AffineWeil.basePointsEquiv (UnramifiedClosure F) E.L
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)
          (GaloisPointComparison.rationalCoeffEquiv (UnramifiedClosure F)
            (AffineWeil.groupScheme (UnramifiedClosure F) E.L
              (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)) x)) := by
  funext x
  simp only [GaloisNorm.rationalPointsEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]

/-- As a set, `weilKernel` is the preimage of `T(L)^b` under the inverse comparison. -/
theorem coe_weilKernel :
    (E.weilKernel : Set (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E.L
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)))) =
      (GaloisNorm.rationalPointsEquiv (UnramifiedClosure F) E.L E.T).symm ⁻¹'
        (characterValuationKernel (intermediateValuation F E.L)
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp) :
            Set (rationalPoints
              (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp))) := by
  rw [weilKernel, Subgroup.map_equiv_eq_comap_symm', Subgroup.coe_comap,
    MulEquiv.coe_toMonoidHom]

/-- `weilKernel` is open in the canonical topology of the Weil restriction's `K`-points. -/
theorem isOpen_weilKernel :
    letI : TopologicalSpace (UnramifiedClosure F) := LocalGalois.Separable.fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E.L
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp))) :=
      rationalPointTopology (UnramifiedClosure F) (AffineWeil.groupScheme (UnramifiedClosure F)
        E.L (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)).X
    IsOpen (E.weilKernel : Set (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F)
      E.L (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)))) := by
  let τK : TopologicalSpace (UnramifiedClosure F) := LocalGalois.Separable.fixedFieldTopology F
  let vL : Valued E.L ℝ≥0 := Valued.mk' (intermediateValuation F E.L)
  have hsmul : ContinuousSMul (UnramifiedClosure F) E.L :=
    intermediateValuation_continuousSMul F E.L
  let τW : TopologicalSpace (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E.L
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp))) :=
    rationalPointTopology (UnramifiedClosure F) (AffineWeil.groupScheme (UnramifiedClosure F)
      E.L (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)).X
  let τL : TopologicalSpace (rationalPoints
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)) :=
    rationalPointTopology E.L
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp).X
  have hk : IsOpen (characterValuationKernel (intermediateValuation F E.L)
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp) :
        Set (rationalPoints
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp))) :=
    E.isOpen_splitCharacterValuationKernel
  have hc : Continuous (fun x : rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E.L
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)) =>
      (GaloisPointComparison.rationalCoeffEquiv E.L
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)).symm
        (AffineWeil.basePointsEquiv (UnramifiedClosure F) E.L
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)
          (GaloisPointComparison.rationalCoeffEquiv (UnramifiedClosure F)
            (AffineWeil.groupScheme (UnramifiedClosure F) E.L
              (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)) x))) :=
    AffineWeil.continuous_rationalBasePoints_of_continuousSMul (UnramifiedClosure F) E.L
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)
  rw [coe_weilKernel, rationalPointsEquiv_symm_eq]
  exact hk.preimage hc

end Weil

/-- `T(K)^0` is open in `T(K)`, given smoothness of the algebraic norm. -/
theorem isOpen_torusIwahori (hnorm : GaloisNormSmoothnessStatement.{u}) :
    letI : TopologicalSpace (UnramifiedClosure F) := LocalGalois.Separable.fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints E.T.toGrp) :=
      rationalPointTopology (UnramifiedClosure F) E.T.toGrp.X
    IsOpen (E.torusIwahori : Set (rationalPoints E.T.toGrp)) := by
  have := E.isAffine_splitTorus
  have := E.locallyOfFiniteType_splitTorus
  let : TopologicalSpace (UnramifiedClosure F) := LocalGalois.Separable.fixedFieldTopology F
  have : Smooth (GaloisNorm.norm (UnramifiedClosure F) E.L E.T).hom.hom.left :=
    hnorm (UnramifiedClosure F) E.L E.T E.isSplitTorus
  have hm := isOpenMap_rationalPoint_of_smooth F henselianSmoothRationalPointOpenMap
    (AffineWeil.groupScheme (UnramifiedClosure F) E.L
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E.L E.T.toGrp)).X E.T.toGrp.X
    (GaloisNorm.norm (UnramifiedClosure F) E.L E.T).hom.hom
  rw [E.torusIwahori_eq_map_weilKernel, Subgroup.coe_map]
  exact hm _ E.isOpen_weilKernel

/-- `H(K)^0` is open in `H(K)`, given smoothness of the norm and of the product map. -/
theorem isOpen_zeroPoints (hprod : DerivedCoverTorusProductSmoothStatement.{u})
    (hnorm : GaloisNormSmoothnessStatement.{u}) [IsAffine H.X.left] :
    letI : TopologicalSpace (UnramifiedClosure F) := LocalGalois.Separable.fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints H) := rationalPointTopology (UnramifiedClosure F) H.X
    IsOpen (E.zeroPoints : Set (rationalPoints H)) := by
  have := E.isAffine_coverTorus
  let : TopologicalSpace (UnramifiedClosure F) := LocalGalois.Separable.fixedFieldTopology F
  have : Smooth (subgroupProductMap (E.π ≫ E.d) E.i).left :=
    hprod (UnramifiedClosure F) H E.D E.C E.T E.d E.π E.i E.isSimplyConnectedDerivedCover
      E.isMaximallySplitMaximalTorus.1
  exact E.isOpen_zeroPoints_of_isOpenMap (E.isOpen_torusIwahori hnorm)
    (isOpenMap_rationalPoint_of_smooth F henselianSmoothRationalPointOpenMap
      (E.C.X ⊗ E.T.toGrp.X) H.X (subgroupProductMap (E.π ≫ E.d) E.i))

end UnramifiedZeroDatum

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- `Z(F)^0` is open in `Z(F)`, in exactly the instances of the published target
`CentralizerZeroCompactOpenStatement`, given smoothness of the norm and of the product map. -/
theorem isOpen_centralizerZero (hprod : DerivedCoverTorusProductSmoothStatement.{u})
    (hnorm : GaloisNormSmoothnessStatement.{u}) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsAffine P.centralizer.Z.X.left := by
      have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
        P.centralizer.isClosedSubgroup
      exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
    letI : TopologicalSpace (rationalPoints P.centralizer.Z) :=
      rationalPointTopology F P.centralizer.Z.X
    IsOpen (P.centralizerZero : Set (rationalPoints P.centralizer.Z)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine P.centralizer.Z.X.left := by
    have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
      P.centralizer.isClosedSubgroup
    exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
  have := P.zeroDatum.centralizerDatum.isAffine_ambient
  exact isOpen_anisotropicZeroPoints_of_isOpen F P.centralizer.Z P.zeroDatum.centralizerDatum
    (P.zeroDatum.centralizerDatum.isOpen_zeroPoints hprod hnorm)

end ParahoricBuildingData

end Langlands.Geometry.Building
