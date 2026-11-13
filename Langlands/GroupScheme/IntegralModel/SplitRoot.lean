import Langlands.GroupScheme.Rational.SplitRootSubgroupOverDomain
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints
import Langlands.GroupScheme.IntegralModelReduction

/-! # Integral root models from an integral split torus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.SplitRoot

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of R))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ M.group)
    (a : characterLattice S) (ha : a ≠ 0)

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom

/-- A chosen actual integral root group supplied by the domain construction. -/
def integralGroup : GroupScheme (Spec (CommRingCat.of R)) :=
  Classical.choose (RelativeRoot.Domain.subgroup_has_smooth_geometricallyConnected_closed_representative
    hS i a ha)

/-- The chosen root group's actual closed inclusion in the integral ambient group. -/
def integralHom : integralGroup M hS i a ha ⟶ M.group :=
  Classical.choose (Classical.choose_spec
    (RelativeRoot.Domain.subgroup_has_smooth_geometricallyConnected_closed_representative
      hS i a ha))

/-- The chosen integral scheme represents the full root functor and has the
proved geometric properties of the domain construction. -/
theorem integral_properties :
    (RelativeRoot.subgroup i a).IsRepresentedBy (integralHom M hS i a ha) ∧
      IsClosedSubgroup (integralHom M hS i a ha) ∧
        IsAffineHom (integralGroup M hS i a ha).X.hom ∧
          Smooth (integralGroup M hS i a ha).X.hom ∧
            GeometricallyConnected (integralGroup M hS i a ha).X.hom :=
  Classical.choose_spec (Classical.choose_spec
    (RelativeRoot.Domain.subgroup_has_smooth_geometricallyConnected_closed_representative
      hS i a ha))

instance integralGroup_affine : IsAffineHom (integralGroup M hS i a ha).X.hom :=
  (integral_properties M hS i a ha).2.2.1

instance integralGroup_smooth : Smooth (integralGroup M hS i a ha).X.hom :=
  (integral_properties M hS i a ha).2.2.2.1

/-- The actual generic fibre of the constructed integral root group. -/
def genericGroup : GroupScheme (Spec (CommRingCat.of K)) :=
  (GroupScheme.baseChange (Spec.algebraMap R K)).obj (integralGroup M hS i a ha)

/-- The root-group map into the specified generic ambient group. -/
def genericHom : genericGroup M hS i a ha ⟶ G :=
  M.genericHom (integralHom M hS i a ha)

/-- The generic fibre represents the full root functor for the base-changed
character and torus map, on every scheme test. -/
theorem isRepresentedBy_genericHom :
    (RelativeRoot.subgroup (M.genericHom i)
      (characterLattice.baseChange (Spec.algebraMap R K) S a)).IsRepresentedBy
        (genericHom M hS i a ha) := by
  let b := Spec.algebraMap R K
  let iK := (GroupScheme.baseChange b).map i
  let aK := characterLattice.baseChange b S a
  have hrep : (RelativeRoot.subgroup iK aK).IsRepresentedBy
      ((GroupScheme.baseChange b).map (integralHom M hS i a ha)) := by
    rw [RelativeRoot.subgroup_baseChange]
    exact (integral_properties M hS i a ha).1.baseChange b
  have htrans : (RelativeRoot.subgroup (M.genericHom i) aK).comap M.genericIso.hom =
      RelativeRoot.subgroup iK aK := by
    simpa only [characterLattice.congr_apply, Iso.refl_inv, Category.id_comp] using
      RelativeRoot.subgroup_comap_of_transport
        (Iso.refl ((CommGroupScheme.baseChange b).obj S)) M.genericIso
        (i := iK) (j := M.genericHom i) (by rfl) aK
  have hp := hrep.comp_iso M.genericIso
  rw [← htrans, ← SubgroupFunctor.comap_comp, Iso.inv_hom_id,
    SubgroupFunctor.comap_id] at hp
  exact hp

/-- A smooth affine integral model of the actual generic root representative. -/
def model : IntegralModel R K (genericGroup M hS i a ha) where
  group := integralGroup M hS i a ha
  genericIso := Iso.refl _

/-- The actual integral inclusion extends the constructed generic inclusion. -/
def inclusion : (model M hS i a ha).Hom M (genericHom M hS i a ha) where
  hom := integralHom M hS i a ha
  generic_comm := by
    change _ = 𝟙 _ ≫ _
    exact (Category.id_comp _).symm

theorem model_isSmooth : (model M hS i a ha).IsSmooth :=
  (integral_properties M hS i a ha).2.2.2.1

theorem model_hasGeometricallyConnectedFibres :
    (model M hS i a ha).HasGeometricallyConnectedFibres :=
  (integral_properties M hS i a ha).2.2.2.2

/-- The model inclusion is an actual closed immersion over the integral base. -/
theorem inclusion_isClosedSubgroup : IsClosedSubgroup (inclusion M hS i a ha).hom :=
  (integral_properties M hS i a ha).2.1

/-- Its exact generic point image is the intersection of ambient integral
points with the full root-subgroup points. -/
theorem map_integralPoints_eq :
    (model M hS i a ha).integralPoints.map (rationalPoints.map (genericHom M hS i a ha)) =
      M.integralPoints ⊓
        (RelativeRoot.subgroup (M.genericHom i)
          (characterLattice.baseChange (Spec.algebraMap R K) S a)).carrier
            (Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
  have hrange : (rationalPoints.map (genericHom M hS i a ha)).range =
      (RelativeRoot.subgroup (M.genericHom i)
        (characterLattice.baseChange (Spec.algebraMap R K) S a)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of K)))) :=
    congrArg (fun F => F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of K)))))
      (isRepresentedBy_genericHom M hS i a ha).2
  rw [← hrange]
  refine Eq.trans ?_ (M.integralPoints_inf_range_genericHom
    (integralHom M hS i a ha) (inclusion_isClosedSubgroup M hS i a ha)).symm
  change ((model M hS i a ha).integralPointMap.range).map
    (rationalPoints.map (genericHom M hS i a ha)) = _
  rw [MonoidHom.map_range]
  congr 1
  apply MonoidHom.ext
  intro x
  exact ((inclusion M hS i a ha).integralPointMap_naturality x).symm

end Langlands.GroupScheme.IntegralModel.SplitRoot
