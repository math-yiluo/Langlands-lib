import Langlands.Geometry.FormalGroup.AtlasOrderRationalTransition
import Langlands.Geometry.FormalGroup.AtlasTangentModule

/-! # The full order action on the compatible tangent module -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {I : Type} [Finite I] {X : BasicAtlas O R I}
variable (E : OrderAction D X)

/-- The order's actual tangent representation on a test algebra in one chart. -/
def chartTangent (A : CommAlgCat.{v} R) (a : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) : D →+* Module.End A (I → A) :=
  ((E.chart a).map (BasicAtlas.coefficientLift (O := O) a.val A ha)).tangent

/-- The actual chart tangent operation commutes with coefficient maps. -/
theorem chartTangent_natural {A B : CommAlgCat.{v} R} (f : A ⟶ B)
    (a : X.opens) (ha : IsUnit (algebraMap R A a.val))
    (hb : IsUnit (algebraMap R B a.val)) (d : D) (x : I → A) :
    (fun i => f.hom (E.chartTangent A a ha d x i)) =
      E.chartTangent B a hb d (fun i => f.hom (x i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let q := ((E.chart a).action d).toHom.toCoordinateMap
  let α := BasicAtlas.coefficientLift (O := O) a.val A ha
  let β := BasicAtlas.coefficientLift (O := O) a.val B hb
  have h := BasicAtlas.coefficientLift_comp (O := O) a.val f ha hb
  funext i
  change f.hom ((q.map α.toRingHom).linearPart x i) = (q.map β.toRingHom).linearPart (fun j => f.hom (x j)) i
  simp only [CoordinateMap.linearPart_apply, CoordinateMap.linearCoeff_map, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (· * f.hom (x j)) (AlgHom.congr_fun h (q.linearCoeff i j))

/-- Differentiation of an order-linear formal transition intertwines the tangent actions. -/
theorem chartTangent_transition (A : CommAlgCat.{v} R) (a b : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (d : D) (x : I → A) :
    X.transitionTangent A a b ha hb (E.chartTangent A a ha d x) =
      E.chartTangent A b hb d (X.transitionTangent A a b ha hb x) :=
  LinearMap.congr_fun ((E.transitionIso A a b ha hb).hom.tangent_commutes d) x

variable (A : CommAlgCat.{v} R)

private def localizedTangentAction (d : D) : Module.End A (X.LocalizedTangent A) :=
  LinearMap.pi fun a =>
    ((E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) d).restrictScalars A).comp
      (LinearMap.proj a)

private theorem localizedTangentAction_mem (d : D) (x : X.tangentSubmodule A) :
    E.localizedTangentAction A d x.val ∈ X.tangentSubmodule A := by
  apply (X.mem_tangentSubmodule A _).mpr
  intro a b
  let B := X.overlapAlgebra A a b
  let ha := X.overlapUnitLeft A a b
  let hb := X.overlapUnitRight A a b
  let la := X.overlapFromLeft A a b
  let lb := X.overlapFromRight A a b
  let za : I → B := fun i => la.hom (x.val a i)
  let zb : I → B := fun i => lb.hom (x.val b i)
  have hx : X.transitionTangent B a b ha hb za = zb :=
    (X.mem_tangentSubmodule A x.val).mp x.property a b
  change X.transitionTangent B a b ha hb
      (fun i => la.hom (E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) d (x.val a) i)) =
    fun i => lb.hom (E.chartTangent (X.localAlgebra A b) b (X.localUnit A b) d (x.val b) i)
  rw [E.chartTangent_natural la a (X.localUnit A a) ha d (x.val a),
    E.chartTangent_natural lb b (X.localUnit A b) hb d (x.val b)]
  exact (E.chartTangent_transition B a b ha hb d za).trans (congrArg (E.chartTangent B b hb d) hx)

private def tangentActionEnd (d : D) : Module.End A (X.tangentSubmodule A) :=
  ((E.localizedTangentAction A d).comp (X.tangentSubmodule A).subtype).codRestrict
    (X.tangentSubmodule A) (E.localizedTangentAction_mem A d)

/-- The full order acts linearly on the compatible overlap tangent module. -/
def tangentAction : D →+* Module.End A (X.tangentSubmodule A) where
  toFun := E.tangentActionEnd A
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext a
    change E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) 0 (x.val a) = 0
    rw [map_zero]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext a
    change E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) 1 (x.val a) = x.val a
    rw [map_one]
    rfl
  map_add' d e := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext a
    change E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) (d + e) (x.val a) =
      E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) d (x.val a) +
        E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) e (x.val a)
    rw [map_add, LinearMap.add_apply]
  map_mul' d e := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext a
    change E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) (d * e) (x.val a) =
      E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) d
        (E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) e (x.val a))
    rw [map_mul, Module.End.mul_apply]

@[simp]
theorem tangentAction_apply (d : D) (x : X.tangentSubmodule A) (a : X.opens) :
    (E.tangentAction A d x).val a = E.chartTangent (X.localAlgebra A a) a (X.localUnit A a) d (x.val a) :=
  rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction
