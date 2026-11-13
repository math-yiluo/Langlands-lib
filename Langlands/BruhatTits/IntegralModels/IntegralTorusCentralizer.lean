import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralRoots
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Rational.TorusCentralizerConjugacy
import Langlands.GroupScheme.IntegralModel.SchematicClosure
import Langlands.GroupScheme.RelativeIdentityComponentProperties

/-! # Actual integral centralizers of the apartment split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

set_option maxHeartbeats 800000 in
private theorem centralizer_geometricallyConnected_overRing
    {R : CommRingCat.{u}} {X H : GroupScheme (Spec R)}
    [Smooth X.X.hom] [IsAffineHom X.X.hom] [GeometricallyConnected X.X.hom]
    {T : CommGroupScheme (Spec R)} (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ X) {j : H ⟶ X} (hj : (torusCentralizer t).IsRepresentedBy j) :
    GeometricallyConnected H.X.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ b => ?_⟩
  let Xk := (GroupScheme.baseChange b).obj X
  let tk := (GroupScheme.baseChange b).map t
  have : Smooth Xk.X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd X.X.hom b)
    infer_instance
  have : IsAffineHom Xk.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd X.X.hom b)
    infer_instance
  have : ConnectedSpace Xk.X.left :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := X.X.hom)) k b
  have hrep := hj.baseChange b
  rw [← torusCentralizer_baseChange b t] at hrep
  have hTk : IsSplitTorus ((CommGroupScheme.baseChange b).obj T).toGrp :=
    IsSplitTorus.baseChange b hT
  exact hTk.connectedSpace_centralizer (G := Xk)
    (C := (GroupScheme.baseChange b).obj H) tk hrep

section General

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G Z : GroupScheme (Spec (CommRingCat.of K))}
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} {N : IntegralModel R K G}
    (A : IntegralSplitTorusData N i) [Smooth N.group.X.hom]

namespace IntegralSplitTorusData

local instance : IsAffine N.group.X.left := isAffine_of_isAffineHom N.group.X.hom

/-- The chosen actual smooth closed integral centralizer of the split torus. -/
def centralizerGroup : GroupScheme (Spec (CommRingCat.of R)) :=
  Classical.choose (splitTorusCentralizer_hasSmoothClosedRepresentative_overRing
    A.inclusion A.isSplit (inferInstance : Smooth N.group.X.hom))

/-- The closed inclusion of the actual integral centralizer. -/
def centralizerIntegralInclusion : A.centralizerGroup ⟶ N.group :=
  Classical.choose (Classical.choose_spec
    (splitTorusCentralizer_hasSmoothClosedRepresentative_overRing
      A.inclusion A.isSplit (inferInstance : Smooth N.group.X.hom)))

theorem centralizer_properties :
    IsClosedSubgroup A.centralizerIntegralInclusion ∧
      Smooth A.centralizerGroup.X.hom ∧
        (torusCentralizer A.inclusion).IsRepresentedBy A.centralizerIntegralInclusion :=
  Classical.choose_spec (Classical.choose_spec
    (splitTorusCentralizer_hasSmoothClosedRepresentative_overRing
      A.inclusion A.isSplit (inferInstance : Smooth N.group.X.hom)))

instance centralizerGroup_smooth : Smooth A.centralizerGroup.X.hom :=
  A.centralizer_properties.2.1

instance centralizerGroup_affine : IsAffineHom A.centralizerGroup.X.hom := by
  have : IsClosedImmersion A.centralizerIntegralInclusion.hom.hom.left :=
    A.centralizer_properties.1
  rw [← A.centralizerIntegralInclusion.hom.hom.w]
  infer_instance

private def genericTorusGroupIso :
    ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj A.torus).toGrp ≅ S.toGrp where
  hom := CommGroupScheme.groupHom A.genericIso.hom
  inv := CommGroupScheme.groupHom A.genericIso.inv
  hom_inv_id := congrArg Additive.toMul A.genericIso.hom_inv_id
  inv_hom_id := congrArg Additive.toMul A.genericIso.inv_hom_id

/-- The generic integral-centralizer inclusion represents the prescribed
whole-torus centralizer on all scheme tests. -/
theorem centralizer_generic_isRepresentedBy :
    (torusCentralizer i).IsRepresentedBy (N.genericHom A.centralizerIntegralInclusion) := by
  have hrep := A.centralizer_properties.2.2.baseChange (Spec.algebraMap R K)
  rw [← torusCentralizer_baseChange] at hrep
  exact hrep.torusCentralizer_of_iso_square A.genericTorusGroupIso N.genericIso
    A.generic_comm

variable (j : Z ⟶ G) (hj : (torusCentralizer i).IsRepresentedBy j)

/-- The actual generic-fibre identification with a supplied representative
of the centralizer, determined by its ambient inclusion. -/
def centralizerGenericIso :
    (GroupScheme.baseChange (Spec.algebraMap R K)).obj A.centralizerGroup ≅ Z :=
  A.centralizer_generic_isRepresentedBy.isoOfIsRepresentedBy hj

@[reassoc]
theorem centralizerGenericIso_hom_comp :
    (A.centralizerGenericIso j hj).hom ≫ j = N.genericHom A.centralizerIntegralInclusion :=
  A.centralizer_generic_isRepresentedBy.isoOfIsRepresentedBy_hom_comp hj

/-- The smooth affine integral model of the specified generic centralizer. -/
def centralizerModel : IntegralModel R K Z where
  group := A.centralizerGroup
  genericIso := A.centralizerGenericIso j hj

/-- The actual integral centralizer inclusion extends the original generic
centralizer map. -/
def centralizerModelMap : (A.centralizerModel j hj).Hom N j where
  hom := A.centralizerIntegralInclusion
  generic_comm := (A.centralizerGenericIso_hom_comp j hj).symm

theorem centralizerModel_isSmooth : (A.centralizerModel j hj).IsSmooth :=
  A.centralizer_properties.2.1

theorem centralizerModelMap_isClosedSubgroup :
    IsClosedSubgroup (A.centralizerModelMap j hj).hom :=
  A.centralizer_properties.1

/-- Integrality in the constructed centralizer is exactly integrality of
its specified ambient image. -/
theorem centralizerModel_integralPoints_eq_comap :
    (A.centralizerModel j hj).integralPoints =
      N.integralPoints.comap (rationalPoints.map j) :=
  (A.centralizerModelMap j hj).integralPoints_eq_comap
    (A.centralizerModelMap_isClosedSubgroup j hj)

/-- The point image is exactly the ambient integral points intersected with
the actual full centralizer points. -/
theorem centralizerModel_map_integralPoints_eq :
    (A.centralizerModel j hj).integralPoints.map (rationalPoints.map j) =
      N.integralPoints ⊓
        (torusCentralizer i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
  rw [A.centralizerModel_integralPoints_eq_comap j hj, Subgroup.map_comap_eq, inf_comm]
  exact congrArg (fun P : Subgroup (rationalPoints G) => N.integralPoints ⊓ P)
    (congrArg (fun H => H.carrier (Over.mk (𝟙 (Spec (CommRingCat.of K))))) hj.2)

/-- With geometrically connected ambient fibres, the integral torus
centralizer also has geometrically connected fibres. -/
theorem centralizerModel_hasGeometricallyConnectedFibres
    [GeometricallyConnected N.group.X.hom] :
    (A.centralizerModel j hj).HasGeometricallyConnectedFibres :=
  centralizer_geometricallyConnected_overRing A.isSplit A.inclusion
    A.centralizer_properties.2.2

end IntegralSplitTorusData

end General

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)
    (hN : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))

/-- The split apartment torus, compatibly embedded in the supplied neutral
model, retaining the chosen torus from the full model. -/
def unramifiedNeutralSplitTorusData : IntegralSplitTorusData D.neutral C.i :=
  (unramifiedIntegralSplitTorusData C D.full Ω hN).factorNeutral D

private instance : Smooth D.neutral.group.X.hom := D.neutral_smooth

/-- The actual smooth affine model of C's centralizer obtained inside the
neutral model. -/
def unramifiedNeutralCentralizerModel :
    IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) C.centralizer.Z :=
  (unramifiedNeutralSplitTorusData C D Ω hN).centralizerModel
    C.centralizer.j C.centralizer.isRepresentedBy

/-- Its closed compatible map has generic arrow exactly C.centralizer.j. -/
def unramifiedNeutralCentralizerModelMap :
    (unramifiedNeutralCentralizerModel C D Ω hN).Hom D.neutral C.centralizer.j :=
  (unramifiedNeutralSplitTorusData C D Ω hN).centralizerModelMap
    C.centralizer.j C.centralizer.isRepresentedBy

theorem unramifiedNeutralCentralizerModel_isSmooth :
    (unramifiedNeutralCentralizerModel C D Ω hN).IsSmooth :=
  (unramifiedNeutralSplitTorusData C D Ω hN).centralizerModel_isSmooth
    C.centralizer.j C.centralizer.isRepresentedBy

theorem unramifiedNeutralCentralizerModel_hasGeometricallyConnectedFibres :
    (unramifiedNeutralCentralizerModel C D Ω hN).HasGeometricallyConnectedFibres := by
  obtain ⟨H, j, hj, _, hH⟩ :=
    RelativeIdentityComponent.smoothExistence _ D.full.group D.full_smooth
  let : GeometricallyConnected H.X.hom := hH
  let : GeometricallyConnected D.neutral.group.X.hom :=
    D.isRelativeComponent.geometricallyConnected hj
  exact (unramifiedNeutralSplitTorusData C D Ω hN).centralizerModel_hasGeometricallyConnectedFibres
    C.centralizer.j C.centralizer.isRepresentedBy

theorem unramifiedNeutralCentralizerModelMap_isClosedSubgroup :
    IsClosedSubgroup (unramifiedNeutralCentralizerModelMap C D Ω hN).hom :=
  (unramifiedNeutralSplitTorusData C D Ω hN).centralizerModelMap_isClosedSubgroup
    C.centralizer.j C.centralizer.isRepresentedBy

theorem unramifiedNeutralCentralizerModel_integralPoints_eq_comap :
    (unramifiedNeutralCentralizerModel C D Ω hN).integralPoints =
      D.neutral.integralPoints.comap (rationalPoints.map C.centralizer.j) :=
  (unramifiedNeutralSplitTorusData C D Ω hN).centralizerModel_integralPoints_eq_comap
    C.centralizer.j C.centralizer.isRepresentedBy

end Unramified

end Langlands.BruhatTits.IntegralModels
