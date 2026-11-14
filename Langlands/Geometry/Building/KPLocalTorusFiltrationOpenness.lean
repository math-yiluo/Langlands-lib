import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.Geometry.Building.KPUnramifiedNormedTopology
import Langlands.Geometry.Building.KPCharacterKernelTopology
import Langlands.GroupScheme.AffineWeilRestrictionForwardTopology
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.GroupScheme.Torus.GaloisNormRational
import Langlands.GroupScheme.Torus.GaloisNormSmoothnessProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothOpenMapProof

/-! # Openness of the actual local torus filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.LocalField
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building


section Local

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "K" => UnramifiedClosure F
local notation "Ω" => SeparableClosure F

section Norm

variable (E : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
  [FiniteDimensional (UnramifiedClosure F) E] [IsGalois (UnramifiedClosure F) E]
  (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffine T.X.left]

private theorem localNorm_moduleFree : Module.Free (UnramifiedClosure F) E :=
  Module.Free.of_divisionRing (UnramifiedClosure F) E

private theorem localNorm_moduleProjective : Module.Projective (UnramifiedClosure F) E :=
  @Module.Projective.of_free _ _ _ _ _ (localNorm_moduleFree F E)

attribute [local instance] localNorm_moduleFree localNorm_moduleProjective

section Weil

variable
  [IsAffine (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp).X.left]
  [LocallyOfFiniteType
    (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp).X.hom]

/-- The bounded subgroup `T(L)^b` transported to `K`-points of the Weil restriction
`R_{L/K}(T_L)` by the published rational-point identification. -/
private def localNormWeilKernel : Subgroup (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E
    (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp))) :=
  (characterValuationKernel (intermediateValuation F E)
    (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)).map
      (GaloisNorm.rationalPointsEquiv (UnramifiedClosure F) E T).toMonoidHom

/-- `T(K)^0` is the image of `weilKernel` under the algebraic norm. -/
private theorem localNorm_eq_map_weilKernel :
    torusNormIwahori (UnramifiedClosure F) E (intermediateValuation F E) T = (localNormWeilKernel F E T).map
      (rationalPoints.map (GaloisNorm.norm (UnramifiedClosure F) E T)) := by
  rw [localNormWeilKernel, Subgroup.map_map]
  change Subgroup.map (GaloisPointComparison.rationalNorm (UnramifiedClosure F) E T) _ = _
  congr 1
  refine MonoidHom.ext fun x => ?_
  exact (GaloisNorm.norm_rationalPoints (UnramifiedClosure F) E T x).symm

/-- The inverse of `rationalPointsEquiv`, written as the explicit coefficient composite. -/
private theorem localNorm_rationalPointsEquiv_symm_eq :
    ((GaloisNorm.rationalPointsEquiv (UnramifiedClosure F) E T).symm :
      rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)) →
      rationalPoints (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)) =
      fun x => (GaloisPointComparison.rationalCoeffEquiv E
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)).symm
        (AffineWeil.basePointsEquiv (UnramifiedClosure F) E
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)
          (GaloisPointComparison.rationalCoeffEquiv (UnramifiedClosure F)
            (AffineWeil.groupScheme (UnramifiedClosure F) E
              (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)) x)) := by
  funext x
  simp only [GaloisNorm.rationalPointsEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]

/-- As a set, `weilKernel` is the preimage of `T(L)^b` under the inverse comparison. -/
private theorem localNorm_coe_weilKernel :
    (localNormWeilKernel F E T : Set (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)))) =
      (GaloisNorm.rationalPointsEquiv (UnramifiedClosure F) E T).symm ⁻¹'
        (characterValuationKernel (intermediateValuation F E)
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp) :
            Set (rationalPoints
              (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp))) := by
  rw [localNormWeilKernel, Subgroup.map_equiv_eq_comap_symm', Subgroup.coe_comap,
    MulEquiv.coe_toMonoidHom]

/-- `weilKernel` is open in the canonical topology of the Weil restriction's `K`-points. -/
private theorem localNorm_isOpen_weilKernel
    (hE : IsSplitTorus (baseChanged K E T.toGrp)) :
    letI : TopologicalSpace (UnramifiedClosure F) := LocalGalois.Separable.fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp))) :=
      rationalPointTopology (UnramifiedClosure F) (AffineWeil.groupScheme (UnramifiedClosure F)
        E (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)).X
    IsOpen (localNormWeilKernel F E T : Set (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F)
      E (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)))) := by
  let τK : TopologicalSpace (UnramifiedClosure F) := LocalGalois.Separable.fixedFieldTopology F
  let vL : Valued E ℝ≥0 := Valued.mk' (intermediateValuation F E)
  let : TopologicalSpace E := vL.toUniformSpace.toTopologicalSpace
  have : IsTopologicalDivisionRing E := @Valued.isTopologicalDivisionRing E _ ℝ≥0 _ vL
  have : ContinuousAdd E := inferInstance
  have hsmul : ContinuousSMul (UnramifiedClosure F) E :=
    intermediateValuation_continuousSMul F E
  let τW : TopologicalSpace (rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp))) :=
    rationalPointTopology (UnramifiedClosure F) (AffineWeil.groupScheme (UnramifiedClosure F)
      E (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)).X
  let τL : TopologicalSpace (rationalPoints
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)) :=
    rationalPointTopology E
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp).X
  have hk : IsOpen (characterValuationKernel (intermediateValuation F E)
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp) :
        Set (rationalPoints
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp))) :=
    isOpen_characterValuationKernel_of_isSplitTorus _ hE
  have hc : Continuous (fun x : rationalPoints (AffineWeil.groupScheme (UnramifiedClosure F) E
        (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)) =>
      (GaloisPointComparison.rationalCoeffEquiv E
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)).symm
        (AffineWeil.basePointsEquiv (UnramifiedClosure F) E
          (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)
          (GaloisPointComparison.rationalCoeffEquiv (UnramifiedClosure F)
            (AffineWeil.groupScheme (UnramifiedClosure F) E
              (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)) x))) :=
    AffineWeil.continuous_rationalBasePoints_of_continuousSMul (UnramifiedClosure F) E
      (GaloisPointComparison.baseChanged (UnramifiedClosure F) E T.toGrp)
  rw [localNorm_coe_weilKernel, localNorm_rationalPointsEquiv_symm_eq]
  exact hk.preimage hc

end Weil

/-- The norm Iwahori of an actual torus is open for every finite Galois
splitting field, in the fixed-field rational-point topology. -/
theorem isOpen_localTorusNormIwahori
    (hE : IsSplitTorus (baseChanged K E T.toGrp)) :
    letI : TopologicalSpace K := fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints T.toGrp) :=
      rationalPointTopology K T.toGrp.X
    IsOpen (torusNormIwahori K E (intermediateValuation F E) T :
      Set (rationalPoints T.toGrp)) := by
  have : IsAffine (baseChanged K E T.toGrp).X.left := by
    have : IsAffineHom (baseChanged K E T.toGrp).X.hom := hE.isAffineHom
    exact isAffine_of_isAffineHom (baseChanged K E T.toGrp).X.hom
  have : LocallyOfFiniteType (baseChanged K E T.toGrp).X.hom := by
    have := hE.smooth
    infer_instance
  let : TopologicalSpace K := fixedFieldTopology F
  have : Smooth (GaloisNorm.norm K E T).hom.hom.left :=
    GaloisNormSmoothnessProof.galoisNormSmoothness K E T hE
  have hm := isOpenMap_rationalPoint_of_smooth F henselianSmoothRationalPointOpenMap
    (AffineWeil.groupScheme K E (baseChanged K E T.toGrp)).X T.toGrp.X
    (GaloisNorm.norm K E T).hom.hom
  rw [localNorm_eq_map_weilKernel, Subgroup.coe_map]
  exact hm _ (localNorm_isOpen_weilKernel F E T hE)

end Norm

section Congruence

variable (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
  [IsAffine T.X.left]

/-- The common geometric-character congruence is open at every depth. -/
theorem isOpen_localGeometricCharacterCongruence (hT : IsTorus T.toGrp) (r : ℝ≥0) :
    letI : TopologicalSpace K := fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints T.toGrp) :=
      rationalPointTopology K T.toGrp.X
    IsOpen (localGeometricCharacterCongruence F T r :
      Set (rationalPoints T.toGrp)) := by
  let : NontriviallyNormedField F := Langlands.LocalGalois.localNormedField F
  let : NontriviallyNormedField Ω := sepClosureNormedField F
  let : IsUltrametricDist Ω := by
    apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    intro x y
    exact isNonarchimedean_spectralNorm («K» := F) (L := Ω) x y
  let : TopologicalSpace K := fixedFieldTopology F
  let : Module.Finite ℤ (rationalCharacters (baseChanged K Ω T.toGrp)) :=
    (rationalCharacterLattice Ω _ (hT.baseChange («K» := Ω)).isConnectedReductive_of_fieldSplitting).2
  have hc : Continuous (algebraMap K Ω) := by
    change @Continuous K Ω (fixedFieldTopology F) (sepClosureTopology F) _
    rw [fixedFieldTopology_eq_induced]
    exact continuous_induced_dom
  exact isOpen_extendedCharacterCongruence_log K Ω T.toGrp hc
    (localLogScale F) (localLogScale_pos F) r

end Congruence


/-- Every term of the local torus filtration is open, including depth zero. -/
theorem isOpen_localTorusFiltration
    (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    [IsAffine T.X.left]
    (hT : IsTorus T.toGrp) (r : ℝ≥0) :
    letI : TopologicalSpace K := fixedFieldTopology F
    letI : TopologicalSpace (rationalPoints T.toGrp) :=
      rationalPointTopology K T.toGrp.X
    IsOpen (localTorusFiltration F T hT r : Set (rationalPoints T.toGrp)) := by
  let S := localTorusSplittingData F T hT
  let : TopologicalSpace K := fixedFieldTopology F
  let : TopologicalSpace (rationalPoints T.toGrp) :=
    rationalPointTopology K T.toGrp.X
  have hzero := isOpen_localTorusNormIwahori F S.L T S.splits
  change IsOpen (localTorusFiltrationAtSplitting F S.L T r :
    Set (rationalPoints T.toGrp))
  by_cases hr : r = 0
  · simpa only [hr, localTorusFiltrationAtSplitting_zero] using hzero
  · simpa only [localTorusFiltrationAtSplitting, ite_eq_right hr, Subgroup.coe_inf] using
      hzero.inter (isOpen_localGeometricCharacterCongruence F T hT r)

end Local

end Langlands.Geometry.Building
