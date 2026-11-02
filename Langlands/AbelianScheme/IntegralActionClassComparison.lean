import Langlands.AbelianScheme.IntegralActionRationalIsomorphism
import Langlands.CategoryTheory.RationalizationIntegralInverse

/-! # Integral inverse-multiple criterion for rational action classes -/

noncomputable section

open CategoryTheory AlgebraicGeometry Module

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u uI uA uO

namespace Langlands.AbelianScheme

variable {S S' : Scheme.{u}} {B C : AbelianScheme S} {O : Type uO} [Ring O]

/-- Actual exactly equivariant integral maps with both composites equal to
the same nonzero integer multiple of the corresponding identity. -/
abbrev IntegralActionInverseData
    (a : O →+* CategoryTheory.End B) (a' : O →+* CategoryTheory.End C) :=
  Rationalization.EquivariantIntegralInverseData a a'

namespace IntegralActionInverseData

variable {a : O →+* CategoryTheory.End B} {a' : O →+* CategoryTheory.End C}

/-- All exact integral equations survive arbitrary actual scheme pullback. -/
def baseChange (d : IntegralActionInverseData a a') (c : S' ⟶ S) :
    IntegralActionInverseData
      (baseChangeOrderAction c B a) (baseChangeOrderAction c C a') where
  multiple := d.multiple
  multiple_ne_zero := d.multiple_ne_zero
  hom := (AbelianScheme.baseChange c).map d.hom
  inv := (AbelianScheme.baseChange c).map d.inv
  hom_inv := by
    rw [← Functor.map_comp, d.hom_inv, Functor.map_zsmul,
      (AbelianScheme.baseChange c).map_id]
  inv_hom := by
    rw [← Functor.map_comp, d.inv_hom, Functor.map_zsmul,
      (AbelianScheme.baseChange c).map_id]
  hom_intertwines := by
    intro x
    change (AbelianScheme.baseChange c).map (a x) ≫
        (AbelianScheme.baseChange c).map d.hom =
      (AbelianScheme.baseChange c).map d.hom ≫
        (AbelianScheme.baseChange c).map (a' x)
    rw [← Functor.map_comp, ← Functor.map_comp, d.hom_intertwines]
  inv_intertwines := by
    intro x
    change (AbelianScheme.baseChange c).map (a' x) ≫
        (AbelianScheme.baseChange c).map d.inv =
      (AbelianScheme.baseChange c).map d.inv ≫
        (AbelianScheme.baseChange c).map (a x)
    rw [← Functor.map_comp, ← Functor.map_comp, d.inv_intertwines]

@[simp] theorem baseChange_multiple (d : IntegralActionInverseData a a') (c : S' ⟶ S) :
    (d.baseChange c).multiple = d.multiple := rfl

@[simp] theorem baseChange_hom (d : IntegralActionInverseData a a') (c : S' ⟶ S) :
    (d.baseChange c).hom = (AbelianScheme.baseChange c).map d.hom := rfl

@[simp] theorem baseChange_inv (d : IntegralActionInverseData a a') (c : S' ⟶ S) :
    (d.baseChange c).inv = (AbelianScheme.baseChange c).map d.inv := rfl

end IntegralActionInverseData

section RationalExtension

variable {I : Type uI} {A : Type uA} [Ring A] [Algebra ℚ A]
    {O : Subalgebra ℤ A} [Submodule.IsLattice ℚ O.toSubmodule]
    (b : Basis I ℤ O)
    (a : O →+* CategoryTheory.End B) (a' : O →+* CategoryTheory.End C)

/-- Exact integral inverse-multiple data give an isomorphism of the full
rational extensions, with forward map the rationalized actual integral map. -/
def integralActionInverseDataIso (d : IntegralActionInverseData a a') :
    RationalAlgebraAction.of B (integralActionRationalExtension B b a) ≅
      RationalAlgebraAction.of C (integralActionRationalExtension C b a') :=
  RationalAlgebraAction.isoMk d.toIntegralInverseData.toIso
    (fun x => integralActionRationalExtension_intertwines b a a'
      d.hom d.hom_intertwines x)

/-- Equality in the existing rational-action quotient is equivalent to exact
integral inverse-multiple data on the same actual representatives. -/
theorem integralAction_classOf_eq_iff [Finite I] :
    RationalAlgebraAction.classOf
        (RationalAlgebraAction.of B (integralActionRationalExtension B b a)) =
      RationalAlgebraAction.classOf
        (RationalAlgebraAction.of C (integralActionRationalExtension C b a')) ↔
      Nonempty (IntegralActionInverseData a a') := by
  rw [RationalAlgebraAction.classOf_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨(integralActionRationalIsoData b a a' e).toInverseData⟩
  · rintro ⟨d⟩
    exact ⟨integralActionInverseDataIso b a a' d⟩

end RationalExtension

end Langlands.AbelianScheme
