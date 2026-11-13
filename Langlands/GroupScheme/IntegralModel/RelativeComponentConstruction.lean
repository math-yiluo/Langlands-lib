import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothBaseChangeProof
import Langlands.GroupScheme.RelativeIdentityComponentDvrAffinenessProof
import Langlands.GroupScheme.RelativeIdentityComponent.OpenConstruction

/-! # The relative identity component of a smooth integral model

Over a discrete valuation ring `R` with fraction field `K`, let `M` be a smooth integral model
of a group `G` over `K` whose structure morphism is geometrically connected. The actual
relative identity component `H ⟶ M.group` is again an integral model of `G`: it is affine
over `R`, smooth, has geometrically connected fibres, and its generic fibre is all of the
generic fibre of `M`. This module constructs that model and its inclusion, and packages both
as `RelativeComponentModelData`. It also shows that homomorphisms from group schemes with
geometrically connected structure morphism (for example split tori) factor through the
relative identity component, and that closed subgroups stay closed.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsRelativeIdentityComponent

variable {S : Scheme.{u}} {G H : GroupScheme S} {i : H ⟶ G}

/-- The inclusion of a represented relative identity component is a monomorphism over the
base. -/
theorem mono_hom (hi : IsRelativeIdentityComponent G i) : Mono i.hom.hom := by
  have : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  infer_instance

/-- A point on a geometrically connected test scheme which has a section mapping to the unit
factors through the relative identity component. -/
theorem exists_lift_of_geometricallyConnected (hi : IsRelativeIdentityComponent G i)
    {T : Over S} [GeometricallyConnected T.hom] (x : T ⟶ G.X) (a : 𝟙_ (Over S) ⟶ T)
    (ha : a ≫ x = η[G.X]) : ∃ y : T ⟶ H.X, y ≫ i.hom.hom = x :=
  (hi.factors_iff T x).mpr
    (RelativeIdentityComponent.inRelativeIdentityComponent_of_geometricallyConnected G x a ha)

/-- Every homomorphism from a group scheme with geometrically connected structure morphism
factors, as a homomorphism, through the relative identity component. -/
theorem exists_hom_lift (hi : IsRelativeIdentityComponent G i) {T : GroupScheme S}
    [GeometricallyConnected T.X.hom] (j : T ⟶ G) : ∃ y : T ⟶ H, y ≫ i = j := by
  obtain ⟨y, hy⟩ := hi.exists_lift_of_geometricallyConnected j.hom.hom η[T.X]
    (IsMonHom.one_hom _)
  have hm : Mono i.hom.hom := hi.mono_hom
  have one_y : η[T.X] ≫ y = η[H.X] := by
    apply hm.right_cancellation
    rw [Category.assoc, hy, IsMonHom.one_hom, IsMonHom.one_hom]
  have mul_y : μ[T.X] ≫ y = (y ⊗ₘ y) ≫ μ[H.X] := by
    apply hm.right_cancellation
    rw [Category.assoc, hy, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      ← Category.assoc, tensorHom_comp_tensorHom, hy]
  refine ⟨Grp.homMk'' y one_y mul_y, ?_⟩
  apply Grp.hom_ext
  exact hy

/-- A factorization of a closed subgroup through the relative identity component is again a
closed subgroup. -/
theorem isClosedSubgroup_of_comp (hi : IsRelativeIdentityComponent G i) {T : GroupScheme S}
    {y : T ⟶ H} (h : IsClosedSubgroup (y ≫ i)) : IsClosedSubgroup y := by
  have : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  have : IsClosedImmersion (y.hom.hom.left ≫ i.hom.hom.left) := h
  exact IsClosedImmersion.of_comp y.hom.hom.left i.hom.hom.left

/-- If the ambient structure morphism is geometrically connected, the inclusion of the
relative identity component is an isomorphism over the base. -/
theorem isIso_hom_of_geometricallyConnected (hi : IsRelativeIdentityComponent G i)
    [GeometricallyConnected G.X.hom] : IsIso i.hom.hom := by
  obtain ⟨y, hy⟩ := hi.exists_lift_of_geometricallyConnected (𝟙 G.X) η[G.X]
    (Category.comp_id _)
  have hm : Mono i.hom.hom := hi.mono_hom
  refine ⟨y, ?_, hy⟩
  apply hm.right_cancellation
  rw [Category.assoc, hy, Category.comp_id, Category.id_comp]

/-- The relative identity component of a group scheme with geometrically connected structure
morphism is the whole group scheme. -/
def isoOfGeometricallyConnected (hi : IsRelativeIdentityComponent G i)
    [GeometricallyConnected G.X.hom] : H ≅ G :=
  haveI := hi.isIso_hom_of_geometricallyConnected
  Grp.mkIso (asIso i.hom.hom) (IsMonHom.one_hom i.hom.hom) (IsMonHom.mul_hom i.hom.hom)

@[simp]
theorem isoOfGeometricallyConnected_hom (hi : IsRelativeIdentityComponent G i)
    [GeometricallyConnected G.X.hom] : hi.isoOfGeometricallyConnected.hom = i := by
  apply Grp.hom_ext
  rfl

end IsRelativeIdentityComponent

/-- After base change to a field, a group scheme with geometrically connected structure
morphism has connected total space. -/
theorem connectedSpace_baseChange_of_geometricallyConnected {S : Scheme.{u}} (H : GroupScheme S)
    [GeometricallyConnected H.X.hom] {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) : ConnectedSpace ((baseChange b).obj H).X.left := by
  have : GeometricallyConnected ((baseChange b).obj H).X.hom := by
    change GeometricallyConnected (pullback.snd H.X.hom b)
    infer_instance
  exact GeometricallyConnected.connectedSpace_of_subsingleton ((baseChange b).obj H).X.hom

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

/-- The actual generic fibre of a model of a group with geometrically connected structure
morphism has geometrically connected structure morphism. -/
theorem geometricallyConnected_genericFibre [GeometricallyConnected G.X.hom] :
    GeometricallyConnected M.genericFibre.X.hom := by
  let e : M.genericFibre.X ≅ G.X := (Grp.forget _).mapIso M.genericIso
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hp : IsPullback e.hom.left M.genericFibre.X.hom G.X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact e.hom.w⟩
  exact MorphismProperty.of_isPullback hp ‹GeometricallyConnected G.X.hom›

variable [IsDiscreteValuationRing R]
  {H : GroupScheme (Spec (CommRingCat.of R))} {i : H ⟶ M.group}

/-- The generic fibre of the relative identity component of a smooth model of a geometrically
connected group is the whole generic fibre of the model, through the generic fibre of the
inclusion. -/
def neutralGenericIso [GeometricallyConnected G.X.hom] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) :
    (baseChange (Spec.algebraMap R K)).obj H ≅ M.genericFibre :=
  haveI := M.geometricallyConnected_genericFibre
  (RelativeIdentityComponent.smoothBaseChange _ M.group hM H i hi _
    (Spec.algebraMap R K)).isoOfGeometricallyConnected

omit [IsDiscreteValuationRing R] in
@[simp]
theorem neutralGenericIso_hom [GeometricallyConnected G.X.hom] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) :
    (M.neutralGenericIso hM hi).hom = (baseChange (Spec.algebraMap R K)).map i := by
  have := M.geometricallyConnected_genericFibre
  exact IsRelativeIdentityComponent.isoOfGeometricallyConnected_hom _

/-- The relative identity component of a smooth model of a geometrically connected group,
as an integral model of the same group. -/
def neutralModel [GeometricallyConnected G.X.hom] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom) : IntegralModel R K G where
  group := H
  affine := RelativeIdentityComponent.smoothDvrAffineness R M.group hM M.affine H i hi
  flat := inferInstance
  finiteType := inferInstance
  genericIso := M.neutralGenericIso hM hi ≪≫ M.genericIso

@[simp]
theorem neutralModel_group [GeometricallyConnected G.X.hom] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom) :
    (M.neutralModel hM hi hH).group = H := rfl

theorem neutralModel_isSmooth [GeometricallyConnected G.X.hom] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom) :
    (M.neutralModel hM hi hH).IsSmooth := hH

/-- The inclusion of the relative identity component as a model homomorphism over the
identity of the generic group. -/
def neutralInclusion [GeometricallyConnected G.X.hom] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom) :
    (M.neutralModel hM hi hH).Hom M (𝟙 G) where
  hom := i
  generic_comm := by
    change _ = (M.neutralGenericIso hM hi ≪≫ M.genericIso).hom ≫ 𝟙 G
    rw [Iso.trans_hom, neutralGenericIso_hom, Category.comp_id]

theorem neutralInclusion_hom [GeometricallyConnected G.X.hom] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom) :
    (M.neutralInclusion hM hi hH).hom = i := rfl

/-- The relative identity component of a smooth model with geometrically connected generic
group, together with the model itself, as relative-component model data. -/
def relativeComponentModelData [GeometricallyConnected G.X.hom] (hM : M.IsSmooth)
    (hi : IsRelativeIdentityComponent M.group i) (hH : Smooth H.X.hom)
    (hgc : GeometricallyConnected H.X.hom) :
    BruhatTits.IntegralModels.RelativeComponentModelData R K G where
  full := M
  neutral := M.neutralModel hM hi hH
  full_smooth := hM
  neutral_smooth := hH
  neutral_connectedFibres :=
    (M.neutralModel hM hi hH).hasConnectedFibres_of_geometricallyConnected hgc
  inclusion := M.neutralInclusion hM hi hH
  isRelativeComponent := hi

/-- Every smooth model over a discrete valuation ring of a group with geometrically connected
structure morphism is the full model of relative-component model data whose neutral model has
geometrically connected fibres. -/
theorem exists_relativeComponentModelData [GeometricallyConnected G.X.hom] (hM : M.IsSmooth) :
    ∃ D : BruhatTits.IntegralModels.RelativeComponentModelData R K G,
      D.full = M ∧ GeometricallyConnected D.neutral.group.X.hom := by
  obtain ⟨H, i, hi, hH, hgc⟩ := RelativeIdentityComponent.smoothExistence _ M.group hM
  exact ⟨M.relativeComponentModelData hM hi hH hgc, rfl, hgc⟩

end IntegralModel

end Langlands.GroupScheme
