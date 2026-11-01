import Langlands.Topology.GroupAction.CompactLocallyConstantAction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Opposites

/-! # Functorial discrete locally constant functions on compact continuous actions -/

noncomputable section

universe u v w

namespace Langlands.CompactAction

open CategoryTheory Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- Compactness refers to the actual underlying topology of the continuous action. -/
def compactContinuousActionProperty (G : Type v) [Group G] [TopologicalSpace G] :
    ObjectProperty (ContAction TopCat.{u} G) :=
  fun S => CompactSpace S.obj.V

/-- All continuous equivariant maps between actual compact action spaces. -/
abbrev CompactContinuousAction (G : Type v) [Group G] [TopologicalSpace G] :=
  (compactContinuousActionProperty G : ObjectProperty (ContAction TopCat.{u} G)).FullSubcategory

namespace CompactContinuousAction

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance (S : CompactContinuousAction.{u, v} G) : CompactSpace S.obj.obj.V := S.property

local instance (S : CompactContinuousAction.{u, v} G) : MulAction G S.obj.obj.V :=
  inferInstanceAs (MulAction G
    ((forget₂ (Action TopCat.{u} G) TopCat.{u}).obj S.obj.obj))

local instance (S : CompactContinuousAction.{u, v} G) : ContinuousSMul G S.obj.obj.V :=
  S.obj.property

/-- The full discrete function space carries its proved continuous inverse-precomposition action. -/
def locallyConstantAction (S : CompactContinuousAction.{u, v} G) (C : Type w) :
    ContAction TopCat.{max u w} G :=
  DiscreteLocallyConstant.continuousAction (X := S.obj.obj.V) (A := C) G

@[simp]
theorem locallyConstantAction_apply (S : CompactContinuousAction.{u, v} G) {C : Type w}
    (g : G) (f : DiscreteLocallyConstant S.obj.obj.V C) (x : S.obj.obj.V) :
    (DiscreteLocallyConstant.toLocallyConstant
      (ConcreteCategory.hom ((locallyConstantAction S C).obj.ρ g) f)) x =
      f (ConcreteCategory.hom (S.obj.obj.ρ g⁻¹) x) := rfl

/-- Every original continuous equivariant map gives continuous equivariant pullback. -/
def locallyConstantPullback {S T : CompactContinuousAction.{u, v} G}
    (q : S ⟶ T) (C : Type w) :
    locallyConstantAction T C ⟶ locallyConstantAction S C :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom
        ⟨DiscreteLocallyConstant.pullback q.hom.hom.hom.hom,
          continuous_of_discreteTopology⟩
      comm := fun g => by
        apply TopCat.ext
        intro f
        let f' : DiscreteLocallyConstant T.obj.obj.V C := f
        apply DiscreteLocallyConstant.ext
        intro x
        change f' (ConcreteCategory.hom (T.obj.obj.ρ g⁻¹)
            (q.hom.hom.hom x)) =
          f' (q.hom.hom.hom (ConcreteCategory.hom (S.obj.obj.ρ g⁻¹) x))
        exact congrArg f' (congrArg (fun k => k x) (q.hom.hom.comm g⁻¹)).symm }

@[simp]
theorem locallyConstantPullback_apply {S T : CompactContinuousAction.{u, v} G}
    (q : S ⟶ T) {C : Type w} (f : DiscreteLocallyConstant T.obj.obj.V C)
    (x : S.obj.obj.V) :
    (DiscreteLocallyConstant.toLocallyConstant
      ((locallyConstantPullback q C).hom.hom f)) x = f (q.hom.hom.hom x) := rfl

/-- Contravariant locally constant functions retain every equivariant continuous arrow. -/
def locallyConstantFunctor (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (C : Type w) :
    (CompactContinuousAction.{u, v} G)ᵒᵖ ⥤ ContAction TopCat.{max u w} G where
  obj S := locallyConstantAction S.unop C
  map q := locallyConstantPullback q.unop C
  map_id _ := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro f
    apply DiscreteLocallyConstant.ext
    intro x
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro f
    apply DiscreteLocallyConstant.ext
    intro x
    rfl

end CompactContinuousAction
end Langlands.CompactAction
