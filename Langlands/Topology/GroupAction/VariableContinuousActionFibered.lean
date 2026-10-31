import Langlands.Topology.Category.TopologicalGroup
import Langlands.Topology.GroupAction.VariableContinuousAction
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-! # Restriction and the fibration of actual continuous actions -/

noncomputable section

universe u v

namespace Langlands.Topology.VariableContinuousAction

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- Retain the actual topological operator group and continuous homomorphisms. -/
def groupForget : VariableContinuousAction.{u, v} ⥤ TopologicalGroup.{v} where
  obj X := TopologicalGroup.of X.groupType
  map f := f.groupHom
  map_id _ := by apply ContinuousMonoidHom.ext; intro g; rfl
  map_comp _ _ := by apply ContinuousMonoidHom.ext; intro g; rfl

@[simp]
theorem groupForget_map {X Y : VariableContinuousAction.{u, v}} (f : X ⟶ Y) :
    groupForget.map f = f.groupHom := rfl

section Restriction

variable (X : VariableContinuousAction.{u, v})
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restrict the original jointly continuous action using Mathlib's restriction. -/
def restrict (f : H →ₜ* X.groupType) : VariableContinuousAction.{u, v} :=
  ⟨H, (ContAction.res TopCat f).obj X.action⟩

@[simp]
theorem restrict_space (f : H →ₜ* X.groupType) :
    (restrict X f).action.obj.V = X.action.obj.V := rfl

/-- The canonical restriction arrow has the original group map and identity
continuous space map. -/
def restrictionMap (f : H →ₜ* X.groupType) : restrict X f ⟶ X where
  groupHom := f
  spaceMap := 𝟙 X.action.obj.V
  equivariant g := by
    change X.action.obj.ρ (f g) ≫ 𝟙 _ = 𝟙 _ ≫ X.action.obj.ρ (f g)
    simp

@[simp]
theorem restrictionMap_groupHom (f : H →ₜ* X.groupType) :
    (restrictionMap X f).groupHom = f := rfl

@[simp]
theorem restrictionMap_spaceMap (f : H →ₜ* X.groupType) :
    (restrictionMap X f).spaceMap = 𝟙 X.action.obj.V := rfl

/-- Identity restriction is isomorphic to the original action by identity maps. -/
def restrictIdIso : restrict X (ContinuousMonoidHom.id X.groupType) ≅ X where
  hom := restrictionMap X (ContinuousMonoidHom.id X.groupType)
  inv :=
    { groupHom := ContinuousMonoidHom.id X.groupType
      spaceMap := 𝟙 X.action.obj.V
      equivariant g := by
        change X.action.obj.ρ g ≫ 𝟙 _ = 𝟙 _ ≫ X.action.obj.ρ g
        simp }
  hom_inv_id := by apply Hom.ext <;> rfl
  inv_hom_id := by apply Hom.ext <;> rfl

variable {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

/-- Successive restriction agrees with composite restriction through identity
group and space comparison maps. -/
def restrictCompIso (f : H →ₜ* X.groupType) (g : J →ₜ* H) :
    restrict (restrict X f) g ≅ restrict X (f.comp g) where
  hom :=
    { groupHom := ContinuousMonoidHom.id J
      spaceMap := 𝟙 X.action.obj.V
      equivariant h := by
        change X.action.obj.ρ (f (g h)) ≫ 𝟙 _ = 𝟙 _ ≫ X.action.obj.ρ (f (g h))
        simp }
  inv :=
    { groupHom := ContinuousMonoidHom.id J
      spaceMap := 𝟙 X.action.obj.V
      equivariant h := by
        change X.action.obj.ρ (f (g h)) ≫ 𝟙 _ = 𝟙 _ ≫ X.action.obj.ρ (f (g h))
        simp }
  hom_inv_id := by apply Hom.ext <;> rfl
  inv_hom_id := by apply Hom.ext <;> rfl

/-- The comparison respects the complete canonical restriction arrows. -/
theorem restrictionMap_comp (f : H →ₜ* X.groupType) (g : J →ₜ* H) :
    (restrictCompIso X f g).hom ≫ restrictionMap X (f.comp g) =
      restrictionMap (restrict X f) g ≫ restrictionMap X f := by
  apply Hom.ext <;> rfl

end Restriction

section Lifting

variable {X Z : VariableContinuousAction.{u, v}}
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A compatible group lift keeps the original continuous map of spaces. -/
def restrictionLift (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) : Z ⟶ restrict X f where
  groupHom := k
  spaceMap := h.spaceMap
  equivariant g := by
    change Z.action.obj.ρ g ≫ h.spaceMap = h.spaceMap ≫ X.action.obj.ρ (f (k g))
    rw [show f (k g) = h.groupHom g from
      congrArg (fun q : Z.groupType →ₜ* X.groupType => q g) hgroup]
    exact h.equivariant g

@[simp]
theorem restrictionLift_groupHom (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    (restrictionLift f h k hgroup).groupHom = k := rfl

@[simp]
theorem restrictionLift_spaceMap (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    (restrictionLift f h k hgroup).spaceMap = h.spaceMap := rfl

/-- The constructed lift factors the entire original arrow. -/
theorem restrictionLift_comp_restrictionMap (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    restrictionLift f h k hgroup ≫ restrictionMap X f = h := by
  apply Hom.ext
  · exact hgroup
  · exact Category.comp_id h.spaceMap

/-- Both components of a restriction lift are determined uniquely. -/
theorem restrictionLift_unique (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom)
    (l : Z ⟶ restrict X f) (lgroup : l.groupHom = k)
    (lfactor : l ≫ restrictionMap X f = h) : l = restrictionLift f h k hgroup := by
  apply Hom.ext
  · exact lgroup
  · have hspace := congrArg (fun q : Z ⟶ X => q.spaceMap) lfactor
    change l.spaceMap ≫ 𝟙 _ = h.spaceMap at hspace
    exact (Category.comp_id l.spaceMap).symm.trans hspace

/-- The full unique-lift property for arbitrary continuous group homomorphisms. -/
theorem restrictionLift_existsUnique (f : H →ₜ* X.groupType) (h : Z ⟶ X)
    (k : Z.groupType →ₜ* H) (hgroup : f.comp k = h.groupHom) :
    ∃! l : Z ⟶ restrict X f, l.groupHom = k ∧ l ≫ restrictionMap X f = h := by
  refine ⟨restrictionLift f h k hgroup,
    ⟨rfl, restrictionLift_comp_restrictionMap f h k hgroup⟩, ?_⟩
  intro l hl
  exact restrictionLift_unique f h k hgroup l hl.1 hl.2

/-- Composition with the canonical arrow identifies the morphism sets over
the prescribed group maps. -/
def restrictionHomEquiv (f : H →ₜ* X.groupType) (k : Z.groupType →ₜ* H) :
    {l : Z ⟶ restrict X f // l.groupHom = k} ≃
      {h : Z ⟶ X // f.comp k = h.groupHom} where
  toFun l := ⟨l.val ≫ restrictionMap X f, by
    change f.comp k = f.comp l.val.groupHom
    rw [l.property]⟩
  invFun h := ⟨restrictionLift f h.val k h.property, rfl⟩
  left_inv l := by
    apply Subtype.ext
    apply Hom.ext
    · exact l.property.symm
    · exact Category.comp_id l.val.spaceMap
  right_inv h := by
    apply Subtype.ext
    exact restrictionLift_comp_restrictionMap f h.val k h.property

end Lifting

/-- Canonical restriction is strongly Cartesian for the actual group functor. -/
instance restrictionMap_isStronglyCartesian (X : VariableContinuousAction.{u, v})
    (H : TopologicalGroup.{v}) (f : H ⟶ groupForget.obj X) :
    Functor.IsStronglyCartesian groupForget f (restrictionMap X f) where
  toIsHomLift := IsHomLift.map groupForget (restrictionMap X f)
  universal_property' := by
    intro Z k h hh
    have hgroup : f.comp k = h.groupHom :=
      IsHomLift.eq_of_isHomLift groupForget (k ≫ f) h
    obtain ⟨l, hl, huniq⟩ := restrictionLift_existsUnique f h k hgroup
    refine ⟨l, ⟨?_, hl.2⟩, ?_⟩
    · have hlgroup : groupForget.map l = k := hl.1
      rw [← hlgroup]
      exact IsHomLift.map groupForget l
    · intro m hm
      apply huniq m
      refine ⟨?_, hm.2⟩
      exact (@IsHomLift.eq_of_isHomLift _ _ _ _ groupForget _ _ k m hm.1).symm

/-- Actual jointly continuous actions form a fibered category over actual
topological groups. -/
instance groupForget_isFibered :
    (groupForget : VariableContinuousAction.{u, v} ⥤ TopologicalGroup.{v}).IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian fun X _H f =>
    ⟨restrict X f, restrictionMap X f, inferInstance⟩

end Langlands.Topology.VariableContinuousAction
