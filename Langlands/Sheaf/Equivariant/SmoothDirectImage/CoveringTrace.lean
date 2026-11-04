import Langlands.Sheaf.Equivariant.CoveringTrace
import Langlands.Sheaf.Equivariant.SmoothDirectImage.Coefficients

/-! # Finite-covering trace on smooth direct images of full coefficient sheaves -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.SmoothDirectImage

open CategoryTheory Opposite Topology
open Langlands.LocallyConstantCovering
open scoped BigOperators

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
  [∀ y, Finite (f ⁻¹' {y})]

/-- Restrict the full sheaf trace to the actual smooth direct image. Its target
is the unchanged, already smooth locally constant coefficient sheaf. -/
def coefficientTrace (h : IsCoveringMap f) (M : Langlands.SmoothRep.{u, u, u} R G) :
    (functor f hf).obj ((LocallyConstantSheaf.smoothFunctor R G X).obj M) ⟶
      (LocallyConstantSheaf.smoothFunctor R G Y).obj M :=
  ObjectProperty.homMk
    ((inclusion f hf).app ((LocallyConstantSheaf.smoothFunctor R G X).obj M) ≫
      DirectImage.coefficientTrace f hf h M.representation)

/-- Forgetting smoothness gives precisely inclusion followed by the full trace. -/
@[simp]
theorem coefficientTrace_forget (h : IsCoveringMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (smoothInclusion R G Y).map (coefficientTrace f hf h M) =
      (inclusion f hf).app ((LocallyConstantSheaf.smoothFunctor R G X).obj M) ≫
        DirectImage.coefficientTrace f hf h M.representation := rfl

/-- The trace acts on the original underlying section, not its smoothness proof. -/
@[simp]
theorem coefficientTrace_apply (h : IsCoveringMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) (U : ActionOpens G Y)
    (s : ((functor f hf).obj
      ((LocallyConstantSheaf.smoothFunctor R G X).obj M)).obj.obj.obj (op U))
    (y : U.openSet) :
    LocallyConstant.toFun (((coefficientTrace f hf h M).hom.hom.app (op U)).hom s) y =
      fiberSum (DirectImage.pointMap f hf U)
        (LocallyConstant.toFun
          (s.val : LocallyConstant ((DirectImage.preimage f hf).obj U).openSet M)) y := rfl

/-- The sum still runs over every point of the original fiber, including empty fibers. -/
theorem coefficientTrace_apply_sum (h : IsCoveringMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) (U : ActionOpens G Y)
    (s : ((functor f hf).obj
      ((LocallyConstantSheaf.smoothFunctor R G X).obj M)).obj.obj.obj (op U))
    (y : U.openSet) [Fintype (f ⁻¹' {y.val})] :
    LocallyConstant.toFun (((coefficientTrace f hf h M).hom.hom.app (op U)).hom s) y =
      ∑ x : f ⁻¹' {y.val},
        (LocallyConstant.toFun
          (s.val : LocallyConstant ((DirectImage.preimage f hf).obj U).openSet M)) ⟨x.val, by
        change f x.val ∈ U.openSet
        rw [show f x.val = y.val from x.property]
        exact y.property⟩ :=
  DirectImage.coefficientTrace_apply_sum f hf h M.representation U s.val y

/-- Smooth pullback followed by trace counts the entire original fiber. -/
theorem coefficientTrace_pullback_apply (h : IsCoveringMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) (U : ActionOpens G Y)
    (s : LocallyConstant U.openSet M) (y : U.openSet) :
    LocallyConstant.toFun
        (((coefficientMap f hf M ≫ coefficientTrace f hf h M).hom.hom.app (op U)).hom s) y =
      Nat.card (f ⁻¹' {y.val}) • s y :=
  DirectImage.coefficientTrace_pullback_apply f hf h M.representation U s y

/-- Every original smooth coefficient intertwiner commutes with the smooth trace. -/
def coefficientTraceNatTrans (h : IsCoveringMap f) :
    LocallyConstantSheaf.smoothFunctor R G X ⋙ functor f hf ⟶
      LocallyConstantSheaf.smoothFunctor R G Y where
  app M := coefficientTrace f hf h M
  naturality M N a := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact trace_map (DirectImage.pointMap f hf U.unop)
      (DirectImage.pointMap_isCoveringMap f hf h U.unop) (Langlands.SmoothRep.hom a).toLinearMap s.val

/-- The full original naturality square is retained. -/
@[reassoc]
theorem coefficientTrace_naturality (h : IsCoveringMap f)
    {M N : Langlands.SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (functor f hf).map ((LocallyConstantSheaf.smoothFunctor R G X).map a) ≫
        coefficientTrace f hf h N =
      coefficientTrace f hf h M ≫ (LocallyConstantSheaf.smoothFunctor R G Y).map a :=
  (coefficientTraceNatTrans f hf h).naturality a

section Identity

local instance finite_identityFiber :
    ∀ x : X, Finite ((ContinuousMap.id X) ⁻¹' {x}) := finite_id_fiber

/-- Identity trace inverts the existing smooth-direct-image unit. -/
@[simp]
theorem coefficientTrace_unit (M : Langlands.SmoothRep.{u, u, u} R G) :
    (idIso (R := R) (G := G) (X := X)).hom.app
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) ≫
      coefficientTrace (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isCoveringMap_id M =
      𝟙 ((LocallyConstantSheaf.smoothFunctor R G X).obj M) := by
  apply ObjectProperty.hom_ext
  change DirectImage.coefficientTrace (ContinuousMap.id X)
    (fun (_ : G) (_ : X) => rfl) isCoveringMap_id M.representation = 𝟙 _
  exact DirectImage.coefficientTrace_id M.representation

/-- The trace for the identity covering is the inverse comparison. -/
@[simp]
theorem coefficientTrace_id (M : Langlands.SmoothRep.{u, u, u} R G) :
    coefficientTrace (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isCoveringMap_id M =
      (idIso (R := R) (G := G) (X := X)).inv.app
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) := by
  apply (cancel_epi ((idIso (R := R) (G := G) (X := X)).hom.app
    ((LocallyConstantSheaf.smoothFunctor R G X).obj M))).mp
  rw [coefficientTrace_unit, Iso.hom_inv_id_app]
  rfl

/-- The identity law is natural in the entire original smooth coefficient category. -/
@[simp]
theorem coefficientTraceNatTrans_id :
    coefficientTraceNatTrans (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) isCoveringMap_id =
      Functor.whiskerLeft (LocallyConstantSheaf.smoothFunctor R G X)
        (idIso (R := R) (G := G) (X := X)).inv := by
  apply NatTrans.ext
  funext M
  exact coefficientTrace_id M

end Identity

/-- Successive smooth traces agree with the composite trace after the actual
lax comparison from iterated to composite smooth direct image. -/
theorem coefficientTrace_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    [∀ z, Finite (g ⁻¹' {z})] [∀ z, Finite ((g.comp f) ⁻¹' {z})]
    (h : IsCoveringMap f) (h' : IsCoveringMap g) (hcomp : IsCoveringMap (g.comp f))
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (compMap f hf g hg).app ((LocallyConstantSheaf.smoothFunctor R G X).obj M) ≫
        coefficientTrace (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) hcomp M =
      (functor g hg).map (coefficientTrace f hf h M) ≫
        coefficientTrace g hg h' M := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact congrArg (fun k => (k.hom.app U).hom s.val.val)
    (DirectImage.coefficientTrace_comp f hf g hg h h' hcomp M.representation)

/-- Composition of smooth traces preserves all original coefficient intertwiners. -/
theorem coefficientTraceNatTrans_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    [∀ z, Finite (g ⁻¹' {z})] [∀ z, Finite ((g.comp f) ⁻¹' {z})]
    (h : IsCoveringMap f) (h' : IsCoveringMap g) (hcomp : IsCoveringMap (g.comp f)) :
    Functor.whiskerLeft (LocallyConstantSheaf.smoothFunctor R G X) (compMap f hf g hg) ≫
        coefficientTraceNatTrans (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) hcomp =
      Functor.whiskerRight (coefficientTraceNatTrans f hf h) (functor g hg) ≫
        coefficientTraceNatTrans g hg h' := by
  apply NatTrans.ext
  funext M
  exact coefficientTrace_comp f hf g hg h h' hcomp M

end Langlands.Sheaf.Equivariant.SmoothDirectImage
