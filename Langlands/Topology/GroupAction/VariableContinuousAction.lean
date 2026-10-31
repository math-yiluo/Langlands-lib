import Mathlib.CategoryTheory.Action.Continuous
import Langlands.CategoryTheory.TopCatSelfForget

/-! # Continuous spaces with varying topological operator groups -/

noncomputable section

universe u v

namespace Langlands.Topology

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- An actual jointly continuous action, with its topological group retained. -/
structure VariableContinuousAction where
  groupType : Type v
  [group : Group groupType]
  [topology : TopologicalSpace groupType]
  [topologicalGroup : IsTopologicalGroup groupType]
  action : ContAction TopCat.{u} groupType

attribute [instance] VariableContinuousAction.group VariableContinuousAction.topology
  VariableContinuousAction.topologicalGroup

namespace VariableContinuousAction

/-- The group homomorphism and continuous space map have the same direction. -/
structure Hom (X Y : VariableContinuousAction.{u, v}) where
  groupHom : X.groupType →ₜ* Y.groupType
  spaceMap : X.action.obj.V ⟶ Y.action.obj.V
  equivariant : ∀ g : X.groupType,
    X.action.obj.ρ g ≫ spaceMap = spaceMap ≫ Y.action.obj.ρ (groupHom g)

@[ext]
theorem Hom.ext {X Y : VariableContinuousAction.{u, v}} {f g : Hom X Y}
    (hgroup : f.groupHom = g.groupHom) (hspace : f.spaceMap = g.spaceMap) : f = g := by
  cases f
  cases g
  cases hgroup
  cases hspace
  rfl

/-- Identity on both the group and the actual topological space. -/
def Hom.id (X : VariableContinuousAction.{u, v}) : Hom X X where
  groupHom := ContinuousMonoidHom.id X.groupType
  spaceMap := 𝟙 X.action.obj.V
  equivariant _ := by simp

/-- Compose the actual group homomorphisms and continuous equivariant maps. -/
def Hom.comp {X Y Z : VariableContinuousAction.{u, v}} (f : Hom X Y) (g : Hom Y Z) :
    Hom X Z where
  groupHom := g.groupHom.comp f.groupHom
  spaceMap := f.spaceMap ≫ g.spaceMap
  equivariant h := by
    change X.action.obj.ρ h ≫ f.spaceMap ≫ g.spaceMap =
      (f.spaceMap ≫ g.spaceMap) ≫ Z.action.obj.ρ (g.groupHom (f.groupHom h))
    rw [← Category.assoc, f.equivariant, Category.assoc, g.equivariant,
      Category.assoc]

instance : Category (VariableContinuousAction.{u, v}) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    · ext h; rfl
    · exact Category.id_comp _
  comp_id f := by
    apply Hom.ext
    · ext h; rfl
    · exact Category.comp_id _
  assoc f g h := by
    apply Hom.ext
    · ext a; rfl
    · exact Category.assoc _ _ _

@[simp]
theorem id_groupHom (X : VariableContinuousAction.{u, v}) :
    (𝟙 X : X ⟶ X).groupHom = ContinuousMonoidHom.id X.groupType := rfl

@[simp]
theorem comp_groupHom {X Y Z : VariableContinuousAction.{u, v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).groupHom = g.groupHom.comp f.groupHom := rfl

@[simp]
theorem comp_spaceMap {X Y Z : VariableContinuousAction.{u, v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).spaceMap = f.spaceMap ≫ g.spaceMap := rfl

/-- Forget only the operator group and its action. -/
def forget : VariableContinuousAction.{u, v} ⥤ TopCat.{u} where
  obj X := X.action.obj.V
  map f := f.spaceMap

section FixedGroup

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Fixed-group continuous equivariant maps use the identity group homomorphism. -/
def ofFixed : ContAction TopCat.{u} G ⥤ VariableContinuousAction.{u, v} where
  obj X := ⟨G, X⟩
  map f :=
    { groupHom := ContinuousMonoidHom.id G
      spaceMap := f.hom.hom
      equivariant := f.hom.comm }
  map_id _ := by apply Hom.ext <;> rfl
  map_comp _ _ := by apply Hom.ext <;> rfl

instance :
    (ofFixed G : ContAction TopCat.{u} G ⥤ VariableContinuousAction.{u, v}).Faithful where
  map_injective {X} {Y} f g h := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact congrArg (fun k => k.spaceMap) h

@[simp]
theorem ofFixed_map_groupHom {X Y : ContAction TopCat.{u} G} (f : X ⟶ Y) :
    ((ofFixed G).map f).groupHom = ContinuousMonoidHom.id G := rfl

end FixedGroup

end VariableContinuousAction

end Langlands.Topology
