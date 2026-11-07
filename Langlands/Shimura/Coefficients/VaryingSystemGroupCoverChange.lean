import Langlands.Shimura.Coefficients.VaryingSystemCoverChange

/-! # Coherent associated-system comparison along varying group and cover maps -/

noncomputable section

universe u uI vI uC vC

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.EquivariantDiagram

variable {I : Type uI} [Category.{vI} I] {D E : I ⥤ GrpCat.{u}}
  (C : Type uC) [Category.{vC} C] (φ : D ⟶ E)

/-- Restrict varying group actions along an actual natural group map, retaining the complete diagram. -/
def groupRestriction : EquivariantDiagram E C ⥤ EquivariantDiagram D C where
  obj M :=
    { obj := M.obj
      ρ i := (M.ρ i).comp (φ.app i).hom
      comm {i j} f g := by
        change M.ρ i ((φ.app i).hom g) ≫ M.obj.map f =
          M.obj.map f ≫ M.ρ j ((φ.app j).hom ((D.map f).hom g))
        rw [M.comm]
        exact congrArg (fun b => M.obj.map f ≫ M.ρ j b)
          (congrArg (fun b : D.obj i ⟶ E.obj j => b.hom g) (φ.naturality f)).symm }
  map c :=
    { hom := c.hom
      comm i g := c.comm i ((φ.app i).hom g) }
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

@[simp] theorem groupRestriction_obj_obj (M : EquivariantDiagram E C) :
    ((groupRestriction C φ).obj M).obj = M.obj := rfl

@[simp] theorem groupRestriction_obj_action (M : EquivariantDiagram E C) (i : I) :
    ((groupRestriction C φ).obj M).action i =
      (Action.res C (φ.app i).hom).obj (M.action i) := rfl

@[simp] theorem groupRestriction_map_hom {M N : EquivariantDiagram E C} (c : M ⟶ N) :
    ((groupRestriction C φ).map c).hom = c.hom := rfl

end Langlands.EquivariantDiagram

namespace Langlands.Shimura.Coefficients

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {I : Type uI} [Category.{vI} I] {D E : I ⥤ GrpCat.{u}}
  (φ : D ⟶ E) (Y : EquivariantDiagram D X.Etale)
  (Z : EquivariantDiagram E X.Etale)
  (a : Y ⟶ (EquivariantDiagram.groupRestriction X.Etale φ).obj Z)

local notation "restriction" => EquivariantDiagram.groupRestriction (ModuleCat R) φ
local notation "J" => X.smallEtaleTopology
local notation "restricted" M:arg => (restriction).obj M
local notation "actionMap" i:arg => (EquivariantDiagram.evaluation i).map a

/-- The original cross-cover comparison, natural in the full coefficient diagram. -/
def etaleAssociatedAtGroupCoverChange (i : I) :
    etaleAssociatedAt (R := R) X Z i ⟶ restriction ⋙ etaleAssociatedAt X Y i :=
  Functor.whiskerLeft (EquivariantDiagram.evaluation i)
    (etaleAssociatedCoverChange X (φ.app i).hom (actionMap i))

local notation "comparison" i:arg M:arg =>
  (etaleAssociatedAtGroupCoverChange X R φ Y Z a i).app M
local notation "oldInc" i:arg M:arg => etaleAssociatedInclusion X (Z.action i) ((M).action i)
local notation "newInc" i:arg M:arg =>
  etaleAssociatedInclusion X (Y.action i) ((restricted M).action i)

@[simp] theorem etaleAssociatedAtGroupCoverChange_app
    (i : I) (M : EquivariantDiagram E (ModuleCat.{u} R)) :
    comparison i M = etaleCrossCoverMap X (φ.app i).hom (actionMap i)
      (𝟙 ((Action.res (ModuleCat.{u} R) (φ.app i).hom).obj (M.action i))) := rfl

/-- Pure cover change retains the coefficient and pulls only the actual cover coordinate. -/
theorem etaleAssociatedAtGroupCoverChange_inclusion
    (i : I) (M : EquivariantDiagram E (ModuleCat.{u} R)) :
    comparison i M ≫ newInc i M =
      oldInc i M ≫ coverPullback J (a.hom.app i)
        ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj i)) :=
  etaleCrossCoverMap_identity_inclusion X R (A := Z.action i) (B := Y.action i)
    (φ.app i).hom (actionMap i) (M.action i)

variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
  (hZ : ∀ i, IsFiniteGeometricTorsor X (Z.action i))

local notation "oldSystem" M:arg => etaleAssociatedVaryingSystem X Z hZ M
local notation "newSystem" M:arg => etaleAssociatedVaryingSystem X Y hY (restricted M)

include hY hZ in
/-- Finiteness and geometric torsor properties of both original actions prove cover comparison invertible. -/
theorem etaleAssociatedAtGroupCoverChange_isIso
    (i : I) (M : EquivariantDiagram E (ModuleCat.{u} R)) : IsIso (comparison i M) :=
  etaleAssociatedCoverComparison X (E.obj i) (D.obj i) (Z.action i) (Y.action i)
    (hZ i) (hY i) (φ.app i).hom (actionMap i) R (M.action i)

/-- Actual cover-map naturality and original reductions make the comparison coherent at every index arrow. -/
@[reassoc] theorem etaleAssociatedAtGroupCoverChange_transition
    (M : EquivariantDiagram E (ModuleCat.{u} R)) {i j : I} (f : i ⟶ j) :
    (oldSystem M).map f ≫ comparison j M = comparison i M ≫ (newSystem M).map f := by
  have hcover :
      coverPullback J (a.hom.app j)
          ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j)) ≫
        coverPullback J (Y.obj.map f)
          ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j)) =
      coverPullback J (Z.obj.map f)
          ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j)) ≫
        coverPullback J (a.hom.app i)
          ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j)) := by
    rw [← coverPullback_comp, ← coverPullback_comp]
    exact congrArg (fun b => coverPullback J b
      ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j))) (a.hom.naturality f)
  have hsource :
      (oldSystem M).map f ≫ oldInc j M ≫ coverPullback J (Z.obj.map f)
          ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j)) =
      oldInc i M ≫ (productSheaf J (Z.obj.obj i)).map
        ((constantSheaf J (ModuleCat.{u} R)).map (M.obj.map f)) :=
    etaleAssociatedTransition_inclusion X Z hZ f M
  have htarget :
      (newSystem M).map f ≫ newInc j M ≫ coverPullback J (Y.obj.map f)
          ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j)) =
      newInc i M ≫ (productSheaf J (Y.obj.obj i)).map
        ((constantSheaf J (ModuleCat.{u} R)).map (M.obj.map f)) :=
    etaleAssociatedTransition_inclusion X Y hY f (restricted M)
  apply etaleAssociatedTransition_hom_ext X Y hY f (restricted M)
  simp only [Category.assoc]
  change (oldSystem M).map f ≫ comparison j M ≫ newInc j M ≫
      coverPullback J (Y.obj.map f)
        ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j)) =
    comparison i M ≫ (newSystem M).map f ≫ newInc j M ≫
      coverPullback J (Y.obj.map f)
        ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j))
  have hi := etaleAssociatedAtGroupCoverChange_inclusion X R φ Y Z a i M
  have hj := etaleAssociatedAtGroupCoverChange_inclusion X R φ Y Z a j M
  rw [reassoc_of% hj, htarget, reassoc_of% hi, hcover]
  have hsource' := congrArg (fun b => b ≫ coverPullback J (a.hom.app i)
    ((constantSheaf J (ModuleCat.{u} R)).obj (M.obj.obj j))) hsource
  simpa only [EquivariantDiagram.groupRestriction, Category.assoc, coverPullback_natural]
    using hsource'

include a in
/-- The whole comparison is a natural isomorphism in the original coefficient diagram. -/
def etaleAssociatedVaryingGroupCoverIso :
    etaleAssociatedVaryingSystemFunctor (R := R) X Z hZ ≅
      restriction ⋙ etaleAssociatedVaryingSystemFunctor X Y hY :=
  NatIso.ofComponents (fun M =>
    NatIso.ofComponents (fun i => by
      letI := etaleAssociatedAtGroupCoverChange_isIso X R φ Y Z a hY hZ i M
      change (etaleAssociatedAt X Z i).obj M ≅
        (etaleAssociatedAt X Y i).obj (restricted M)
      exact asIso (comparison i M))
      (fun f => by
        change (oldSystem M).map f ≫ comparison _ M = comparison _ M ≫ (newSystem M).map f
        exact etaleAssociatedAtGroupCoverChange_transition X R φ Y Z a hY hZ M f))
    (fun c => by
      apply NatTrans.ext
      funext i
      exact (etaleAssociatedAtGroupCoverChange X R φ Y Z a i).naturality c)

@[simp] theorem etaleAssociatedVaryingGroupCoverIso_hom_app
    (M : EquivariantDiagram E (ModuleCat.{u} R)) (i : I) :
    ((etaleAssociatedVaryingGroupCoverIso X R φ Y Z a hY hZ).hom.app M).app i =
      comparison i M := rfl

/-- The inverse retains every original index transition as well. -/
@[reassoc] theorem etaleAssociatedVaryingGroupCoverIso_inv_transition
    (M : EquivariantDiagram E (ModuleCat.{u} R)) {i j : I} (f : i ⟶ j) :
    (newSystem M).map f ≫
        ((etaleAssociatedVaryingGroupCoverIso X R φ Y Z a hY hZ).inv.app M).app j =
      ((etaleAssociatedVaryingGroupCoverIso X R φ Y Z a hY hZ).inv.app M).app i ≫
        (oldSystem M).map f :=
  ((etaleAssociatedVaryingGroupCoverIso X R φ Y Z a hY hZ).inv.app M).naturality f

end Langlands.Shimura.Coefficients
