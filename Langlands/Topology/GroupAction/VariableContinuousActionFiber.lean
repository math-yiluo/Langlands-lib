import Langlands.Topology.GroupAction.VariableContinuousActionFibered
import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-! # Fixed-group continuous actions are the actual group-forget fibers -/

noncomputable section

universe u v

namespace Langlands.Topology.VariableContinuousAction

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- The fixed-group inclusion lies strictly over the constant group functor. -/
theorem ofFixed_comp_groupForget (G : TopologicalGroup.{v}) :
    (ofFixed G : ContAction TopCat.{u} G ⥤ _) ⋙ groupForget =
      (Functor.const (ContAction TopCat.{u} G)).obj G := rfl

/-- Retain the actual continuous action and its maps in the standard fiber. -/
def ofFixedToFiber (G : TopologicalGroup.{v}) :
    ContAction TopCat.{u} G ⥤ Functor.Fiber groupForget G :=
  Functor.Fiber.inducedFunctor (ofFixed_comp_groupForget G)

@[simp]
theorem ofFixedToFiber_comp_inclusion (G : TopologicalGroup.{v}) :
    (ofFixedToFiber G : ContAction TopCat.{u} G ⥤ _) ⋙ Functor.Fiber.fiberInclusion =
      ofFixed G := rfl

/-- Recover a fixed-group equivariant map without changing its continuous map. -/
def ofFixedFiberPreimage (G : TopologicalGroup.{v}) {X Y : ContAction TopCat.{u} G}
    (f : (ofFixedToFiber G).obj X ⟶ (ofFixedToFiber G).obj Y) : X ⟶ Y := by
  have hf : f.val.groupHom = ContinuousMonoidHom.id G :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ groupForget
      ((ofFixed G).obj X) ((ofFixed G).obj Y) (𝟙 G) f.val f.property).symm
  exact ObjectProperty.homMk
    { hom := f.val.spaceMap
      comm := fun g => by
        have he := f.val.equivariant g
        change X.obj.ρ g ≫ f.val.spaceMap =
          f.val.spaceMap ≫ Y.obj.ρ (f.val.groupHom g) at he
        rw [hf] at he
        exact he }

@[simp]
theorem ofFixedFiberPreimage_spaceMap (G : TopologicalGroup.{v})
    {X Y : ContAction TopCat.{u} G}
    (f : (ofFixedToFiber G).obj X ⟶ (ofFixedToFiber G).obj Y) :
    (ofFixedFiberPreimage G f).hom.hom = f.val.spaceMap := rfl

@[simp]
theorem ofFixedToFiber_map_preimage (G : TopologicalGroup.{v})
    {X Y : ContAction TopCat.{u} G}
    (f : (ofFixedToFiber G).obj X ⟶ (ofFixedToFiber G).obj Y) :
    (ofFixedToFiber G).map (ofFixedFiberPreimage G f) = f := by
  apply Subtype.ext
  apply Hom.ext
  · exact @IsHomLift.eq_of_isHomLift _ _ _ _ groupForget
      ((ofFixed G).obj X) ((ofFixed G).obj Y) (𝟙 G) f.val f.property
  · rfl

@[simp]
theorem ofFixedFiberPreimage_map (G : TopologicalGroup.{v})
    {X Y : ContAction TopCat.{u} G} (f : X ⟶ Y) :
    ofFixedFiberPreimage G ((ofFixedToFiber G).map f) = f := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  rfl

instance ofFixedToFiber_full (G : TopologicalGroup.{v}) :
    (ofFixedToFiber G : ContAction TopCat.{u} G ⥤ _).Full where
  map_surjective f := ⟨ofFixedFiberPreimage G f, ofFixedToFiber_map_preimage G f⟩

instance ofFixedToFiber_faithful (G : TopologicalGroup.{v}) :
    (ofFixedToFiber G : ContAction TopCat.{u} G ⥤ _).Faithful where
  map_injective {X Y} f g h := by
    apply (ofFixed G).map_injective
    exact congrArg (fun k => k.val) h

/-- Every standard fiber object retains its original fixed-group action. -/
theorem ofFixedToFiber_obj_surjective (G : TopologicalGroup.{v}) :
    Function.Surjective (ofFixedToFiber G : ContAction TopCat.{u} G ⥤ _).obj := by
  rintro ⟨X, hX⟩
  cases hX
  refine ⟨X.action, ?_⟩
  apply Subtype.ext
  cases X
  rfl

instance ofFixedToFiber_essSurj (G : TopologicalGroup.{v}) :
    (ofFixedToFiber G : ContAction TopCat.{u} G ⥤ _).EssSurj :=
  Functor.essSurj_of_surj (ofFixedToFiber_obj_surjective G)

instance ofFixedToFiber_isEquivalence (G : TopologicalGroup.{v}) :
    (ofFixedToFiber G : ContAction TopCat.{u} G ⥤ _).IsEquivalence where

/-- Fixed-group continuous actions are equivalent to the standard fiber. -/
def fixedGroupFiberEquivalence (G : TopologicalGroup.{v}) :
    ContAction TopCat.{u} G ≌ Functor.Fiber groupForget G :=
  (ofFixedToFiber G).asEquivalence

/-- Choose the existing continuous-action categories locally as fibers. -/
@[instance_reducible]
def fixedGroupFibers : HasFibers
    (groupForget : VariableContinuousAction.{u, v} ⥤ TopologicalGroup.{v}) where
  Fib G := ContAction TopCat.{u} G
  ι G := ofFixed G
  comp_const G := ofFixed_comp_groupForget G
  equiv G := by
    change (ofFixedToFiber G : ContAction TopCat.{u} G ⥤ _).IsEquivalence
    exact ofFixedToFiber_isEquivalence G

end Langlands.Topology.VariableContinuousAction
