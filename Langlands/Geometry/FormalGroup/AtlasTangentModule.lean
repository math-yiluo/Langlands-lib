import Langlands.Geometry.FormalGroup.AtlasOverlapPoints
import Langlands.Geometry.FormalGroup.Tangent

/-! # The compatible tangent module of a formal atlas -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {I : Type} [Finite I]
variable (X : BasicAtlas O R I) (A : CommAlgCat.{v} R)

/-- The formal transition differentiates to a linear equivalence of coordinate tangent modules. -/
def transitionTangent (a b : X.opens) (ha : IsUnit (algebraMap R A a.val))
    (hb : IsUnit (algebraMap R A b.val)) : (I → A) ≃ₗ[A] (I → A) :=
  (X.transition A a b ha hb).tangent

@[simp]
theorem transitionTangent_self (a : X.opens) (ha : IsUnit (algebraMap R A a.val)) :
    X.transitionTangent A a a ha ha = LinearEquiv.refl A (I → A) := by
  rw [transitionTangent, X.transition_self]
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun
    (ModuleLaw.Hom.tangent_id
      (M := (X.chart a).map (BasicAtlas.coefficientLift (O := O) a.val A ha))) x

/-- The chart change on coordinate tangent modules inherits the formal cocycle. -/
theorem transitionTangent_cocycle (a b c : X.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (hc : IsUnit (algebraMap R A c.val)) :
    (X.transitionTangent A a b ha hb).trans (X.transitionTangent A b c hb hc) =
      X.transitionTangent A a c ha hc := by
  apply LinearEquiv.ext
  intro x
  have h := congrArg (fun e => e.hom.tangent x) (X.transition_cocycle A a b c ha hb hc)
  exact (LinearMap.congr_fun (ModuleLaw.Hom.tangent_comp
    (X.transition A b c hb hc).hom (X.transition A a b ha hb).hom) x).symm.trans h

/-- Tuples on the universal principal test for each chart. -/
abbrev LocalizedTangent := (a : X.opens) → I → X.localAlgebra A a

/-- The restrictions to an overlap are algebra maps over the original test algebra. -/
def overlapFromLeftAlg (a b : X.opens) : X.localAlgebra A a →ₐ[A] X.overlapAlgebra A a b where
  __ := (X.overlapFromLeft A a b).hom.toRingHom
  commutes' x := congrArg (fun g : A ⟶ X.overlapAlgebra A a b => g.hom x)
    (X.localizationMap_testFactor ⟨X.overlapAlgebra A a b, X.overlapMap A a b, a,
      X.overlapUnitLeft A a b⟩)

/-- The right chart has the corresponding restriction over the test algebra. -/
def overlapFromRightAlg (a b : X.opens) : X.localAlgebra A b →ₐ[A] X.overlapAlgebra A a b where
  __ := (X.overlapFromRight A a b).hom.toRingHom
  commutes' x := congrArg (fun g : A ⟶ X.overlapAlgebra A a b => g.hom x)
    (X.localizationMap_testFactor ⟨X.overlapAlgebra A a b, X.overlapMap A a b, b,
      X.overlapUnitRight A a b⟩)

private def mapTangentVector {S T : Type v} [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
    (f : S →ₐ[A] T) : (I → S) →ₗ[A] (I → T) :=
  LinearMap.pi fun i => f.toLinearMap.comp (LinearMap.proj i)

/-- Take the difference of the two restrictions to every universal chart overlap. -/
def tangentOverlapDifference :
    X.LocalizedTangent A →ₗ[A] ((ab : X.opens × X.opens) → I → X.overlapAlgebra A ab.1 ab.2) :=
  LinearMap.pi fun ab =>
    (((X.transitionTangent (X.overlapAlgebra A ab.1 ab.2) ab.1 ab.2
      (X.overlapUnitLeft A ab.1 ab.2) (X.overlapUnitRight A ab.1 ab.2)).toLinearMap.restrictScalars A).comp
        ((mapTangentVector (I := I) A (X.overlapFromLeftAlg A ab.1 ab.2)).comp (LinearMap.proj ab.1))) -
      (mapTangentVector (I := I) A (X.overlapFromRightAlg A ab.1 ab.2)).comp (LinearMap.proj ab.2)

/-- The actual module of tangent tuples agreeing on the chart overlaps. -/
def tangentSubmodule : Submodule A (X.LocalizedTangent A) :=
  LinearMap.ker (X.tangentOverlapDifference A)

/-- A tuple is in the tangent module exactly when both restrictions agree on every overlap. -/
theorem mem_tangentSubmodule (z : X.LocalizedTangent A) :
    z ∈ X.tangentSubmodule A ↔ ∀ a b : X.opens,
      X.transitionTangent (X.overlapAlgebra A a b) a b
        (X.overlapUnitLeft A a b) (X.overlapUnitRight A a b)
        (fun i => X.overlapFromLeftAlg A a b (z a i)) =
      fun i => X.overlapFromRightAlg A a b (z b i) := by
  change X.tangentOverlapDifference A z = 0 ↔ _
  constructor
  · intro hz a b
    have hab := congrFun hz (a, b)
    exact sub_eq_zero.mp hab
  · intro hz
    funext ab
    exact sub_eq_zero.mpr (hz ab.1 ab.2)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
