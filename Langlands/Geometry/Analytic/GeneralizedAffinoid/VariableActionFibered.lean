import Langlands.Topology.Category.TopologicalGroup
import Langlands.Geometry.Analytic.GeneralizedAffinoid.VariableActionRestrictionLift
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-! # The fibration of actual quotient actions over topological groups -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Retain precisely the actual topological operator group and its continuous
homomorphisms. -/
def groupForget : VariableActionSpace.{u, v} K ⥤ Langlands.Topology.TopologicalGroup.{v} where
  obj X := Langlands.Topology.TopologicalGroup.of X.groupType
  map f := f.groupHom
  map_id X := by apply ContinuousMonoidHom.ext; intro g; rfl
  map_comp f g := by apply ContinuousMonoidHom.ext; intro a; rfl

@[simp]
theorem groupForget_map {X Y : VariableActionSpace.{u, v} K} (f : X ⟶ Y) :
    groupForget.map f = f.groupHom := rfl

/-- Canonical restriction has the full strongly Cartesian universal property
over every continuous homomorphism of topological groups. -/
instance restrictionMap_isStronglyCartesian (X : VariableActionSpace.{u, v} K)
    (H : Langlands.Topology.TopologicalGroup.{v}) (f : H ⟶ groupForget.obj X) :
    Functor.IsStronglyCartesian groupForget f (restrictionMap X f) where
  toIsHomLift := IsHomLift.map (groupForget (K := K)) (restrictionMap X f)
  universal_property' := by
    intro Z k h hh
    have hgroup : f.comp k = h.groupHom :=
      IsHomLift.eq_of_isHomLift groupForget (k ≫ f) h
    obtain ⟨l, hl, huniq⟩ := restrictionLift_existsUnique f h k hgroup
    refine ⟨l, ⟨?_, hl.2⟩, ?_⟩
    · have hlgroup : groupForget.map l = k := hl.1
      rw [← hlgroup]
      exact IsHomLift.map (groupForget (K := K)) l
    · intro m hm
      apply huniq m
      refine ⟨?_, hm.2⟩
      exact (@IsHomLift.eq_of_isHomLift _ _ _ _ (groupForget (K := K))
        _ _ k m hm.1).symm

/-- The category of actual finite positive-polyradius quotient actions is
fibered over the category of topological groups. -/
instance groupForget_isFibered :
    (groupForget : VariableActionSpace.{u, v} K ⥤
      Langlands.Topology.TopologicalGroup.{v}).IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian fun X _H f =>
    ⟨restrict X f, restrictionMap X f, inferInstance⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.VariableActionSpace
