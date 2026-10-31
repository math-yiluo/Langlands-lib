import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Category.TopCat.Basic

/-! # The category of topological groups and continuous group homomorphisms -/

universe v

namespace Langlands.Topology

open CategoryTheory

/-- A group with a topology making multiplication and inversion continuous. -/
structure TopologicalGroup where
  carrier : Type v
  [group : Group carrier]
  [topology : TopologicalSpace carrier]
  [topologicalGroup : IsTopologicalGroup carrier]

attribute [instance] TopologicalGroup.group TopologicalGroup.topology
  TopologicalGroup.topologicalGroup

instance : CoeSort TopologicalGroup (Type v) := ⟨TopologicalGroup.carrier⟩

namespace TopologicalGroup

/-- Bundle an existing topological group without changing any structure. -/
def of (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    TopologicalGroup.{v} := ⟨G⟩

instance : Category TopologicalGroup.{v} where
  Hom G H := G →ₜ* H
  id G := ContinuousMonoidHom.id G
  comp f g := g.comp f
  id_comp f := by ext g; rfl
  comp_id f := by ext g; rfl
  assoc f g h := by ext a; rfl

instance : ConcreteCategory TopologicalGroup.{v} (fun G H => G →ₜ* H) where
  hom f := f
  ofHom f := f

@[ext]
theorem hom_ext {G H : TopologicalGroup.{v}} {f g : G ⟶ H}
    (h : ∀ a : G, f a = g a) : f = g :=
  ContinuousMonoidHom.ext h

@[simp]
theorem id_apply (G : TopologicalGroup.{v}) (g : G) : (𝟙 G : G ⟶ G) g = g := rfl

@[simp]
theorem comp_apply {G H J : TopologicalGroup.{v}} (f : G ⟶ H) (g : H ⟶ J)
    (a : G) : (f ≫ g) a = g (f a) := rfl

/-- Forget the group operations, retaining the actual topology and map. -/
def forget : TopologicalGroup.{v} ⥤ TopCat.{v} where
  obj G := TopCat.of G
  map f := TopCat.ofHom f.toContinuousMap
  map_id G := by ext g; rfl
  map_comp f g := by ext a; rfl

instance : forget.Faithful where
  map_injective {G H} f g h := by
    apply ContinuousMonoidHom.ext
    intro a
    exact congrArg (fun q : TopCat.of G ⟶ TopCat.of H => q a) h

@[simp]
theorem forget_map_apply {G H : TopologicalGroup.{v}} (f : G ⟶ H) (g : G) :
    (forget.map f) g = f g := rfl

end TopologicalGroup

end Langlands.Topology
