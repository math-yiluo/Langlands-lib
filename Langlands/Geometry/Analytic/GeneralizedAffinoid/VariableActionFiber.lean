import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableActionFibered
import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-! # Fixed-group quotient actions are the actual group-forget fibers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- The fixed-group inclusion lies strictly over the constant group functor. -/
theorem ofFixed_comp_groupForget (G : Langlands.Topology.TopologicalGroup.{v}) :
    ofFixed (K := K) G ⋙ groupForget =
      (Functor.const (NormContinuousSpace K G)).obj G := rfl

/-- The existing fixed-group category maps into the actual Mathlib fiber. -/
def ofFixedToFiber (G : Langlands.Topology.TopologicalGroup.{v}) :
    NormContinuousSpace K G ⥤ Functor.Fiber (groupForget (K := K)) G :=
  Functor.Fiber.inducedFunctor (ofFixed_comp_groupForget G)

@[simp]
theorem ofFixedToFiber_comp_inclusion (G : Langlands.Topology.TopologicalGroup.{v}) :
    ofFixedToFiber (K := K) G ⋙ Functor.Fiber.fiberInclusion = ofFixed G := rfl

/-- Recover the original equivariant bounded map from an arrow in the fiber. -/
def ofFixedFiberPreimage (G : Langlands.Topology.TopologicalGroup.{v})
    {X Y : NormContinuousSpace K G}
    (f : (ofFixedToFiber G).obj X ⟶ (ofFixedToFiber G).obj Y) : X ⟶ Y := by
  have hf : f.val.groupHom = ContinuousMonoidHom.id G :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (groupForget (K := K))
      ((ofFixed G).obj X) ((ofFixed G).obj Y) (𝟙 G) f.val f.property).symm
  exact Quiver.Hom.op (NormContinuousAction.homMk f.val.algebraMap (fun g => by
    apply BoundedAlgHom.ext
    intro a
    have he := f.val.equivariant g a
    change f.val.algebraMap ((Y.unop.obj.ρ (f.val.groupHom g)).toAlgHom a) =
      (X.unop.obj.ρ g).toAlgHom (f.val.algebraMap a) at he
    rw [hf] at he
    exact he))

@[simp]
theorem ofFixedToFiber_map_preimage (G : Langlands.Topology.TopologicalGroup.{v})
    {X Y : NormContinuousSpace K G}
    (f : (ofFixedToFiber G).obj X ⟶ (ofFixedToFiber G).obj Y) :
    (ofFixedToFiber G).map (ofFixedFiberPreimage G f) = f := by
  apply Subtype.ext
  apply Hom.ext
  · exact @IsHomLift.eq_of_isHomLift _ _ _ _ (groupForget (K := K))
      ((ofFixed G).obj X) ((ofFixed G).obj Y) (𝟙 G) f.val f.property
  · rfl

@[simp]
theorem ofFixedFiberPreimage_map (G : Langlands.Topology.TopologicalGroup.{v})
    {X Y : NormContinuousSpace K G} (f : X ⟶ Y) :
    ofFixedFiberPreimage G ((ofFixedToFiber G).map f) = f := by
  apply Quiver.Hom.unop_inj
  apply NormContinuousAction.hom_ext
  rfl

instance ofFixedToFiber_full (G : Langlands.Topology.TopologicalGroup.{v}) :
    (ofFixedToFiber (K := K) G).Full where
  map_surjective f := ⟨ofFixedFiberPreimage G f, ofFixedToFiber_map_preimage G f⟩

instance ofFixedToFiber_faithful (G : Langlands.Topology.TopologicalGroup.{v}) :
    (ofFixedToFiber (K := K) G).Faithful where
  map_injective {X Y} f g h := by
    apply (ofFixed G).map_injective
    exact congrArg (fun k => k.val) h

/-- Every actual fiber object comes from its original quotient action. -/
theorem ofFixedToFiber_obj_surjective (G : Langlands.Topology.TopologicalGroup.{v}) :
    Function.Surjective (ofFixedToFiber (K := K) G).obj := by
  rintro ⟨X, hX⟩
  cases hX
  refine ⟨Opposite.op X.algebraAction, ?_⟩
  apply Subtype.ext
  cases X
  rfl

instance ofFixedToFiber_essSurj (G : Langlands.Topology.TopologicalGroup.{v}) :
    (ofFixedToFiber (K := K) G).EssSurj :=
  Functor.essSurj_of_surj (ofFixedToFiber_obj_surjective G)

instance ofFixedToFiber_isEquivalence (G : Langlands.Topology.TopologicalGroup.{v}) :
    (ofFixedToFiber (K := K) G).IsEquivalence where

/-- The fixed-group category is equivalent to the standard fiber. -/
def fixedGroupFiberEquivalence (G : Langlands.Topology.TopologicalGroup.{v}) :
    NormContinuousSpace K G ≌ Functor.Fiber (groupForget (K := K)) G :=
  (ofFixedToFiber G).asEquivalence

/-- The original fixed-group categories provide explicit fibers.
This is a definition so that users choose it locally when using `HasFibers`. -/
@[instance_reducible]
def fixedGroupFibers : HasFibers
    (groupForget : VariableActionSpace.{u, v} K ⥤
      Langlands.Topology.TopologicalGroup.{v}) where
  Fib G := NormContinuousSpace K G
  ι G := ofFixed (K := K) G
  comp_const G := ofFixed_comp_groupForget (K := K) G
  equiv G := by
    change (ofFixedToFiber (K := K) G).IsEquivalence
    exact ofFixedToFiber_isEquivalence G

end Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace
