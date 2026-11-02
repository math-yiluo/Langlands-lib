import Langlands.AbelianScheme.RelativeIntegralActionComparison
import Langlands.AbelianScheme.RationalIntegralComparison
import Langlands.CategoryTheory.RationalizationEquivariantDenominators

/-! # Exactly equivariant integral maps for rational action isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry Module

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u uI uA uO

namespace Langlands.AbelianScheme

variable {S S' : Scheme.{u}} {B C : AbelianScheme S} {O : Type uO} [Ring O]

/-- Actual integral representatives, exact inverse-multiple identities, and
exact equivariance for both integral actions. -/
abbrev EquivariantRationalIsoIntegralData
    (a : O →+* CategoryTheory.End B) (a' : O →+* CategoryTheory.End C)
    (e : Rationalization.of B ≅ Rationalization.of C) :=
  Rationalization.EquivariantIntegralIsoData a a' e

namespace EquivariantRationalIsoIntegralData

variable {a : O →+* CategoryTheory.End B} {a' : O →+* CategoryTheory.End C}
    {e : Rationalization.of B ≅ Rationalization.of C}

/-- Pull back supplied exact equivariant data along an arbitrary scheme map. -/
def baseChange (d : EquivariantRationalIsoIntegralData a a' e) (c : S' ⟶ S) :
    EquivariantRationalIsoIntegralData
      (baseChangeOrderAction c B a) (baseChangeOrderAction c C a')
      (rationalBaseChangeIso c e) where
  toIntegralIsoData := RationalIsoIntegralData.baseChange d.toIntegralIsoData c
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

@[simp]
theorem baseChange_homDenom (d : EquivariantRationalIsoIntegralData a a' e)
    (c : S' ⟶ S) : (d.baseChange c).homDenom = d.homDenom := rfl

@[simp]
theorem baseChange_invDenom (d : EquivariantRationalIsoIntegralData a a' e)
    (c : S' ⟶ S) : (d.baseChange c).invDenom = d.invDenom := rfl

@[simp]
theorem baseChange_hom (d : EquivariantRationalIsoIntegralData a a' e)
    (c : S' ⟶ S) :
    (d.baseChange c).hom = (AbelianScheme.baseChange c).map d.hom := rfl

@[simp]
theorem baseChange_inv (d : EquivariantRationalIsoIntegralData a a' e)
    (c : S' ⟶ S) :
    (d.baseChange c).inv = (AbelianScheme.baseChange c).map d.inv := rfl

end EquivariantRationalIsoIntegralData

section RationalExtension

variable {I : Type uI} [Finite I] {A : Type uA} [Ring A] [Algebra ℚ A]
    {O : Subalgebra ℤ A} [Submodule.IsLattice ℚ O.toSubmodule]
    (b : Basis I ℤ O)
    (a : O →+* CategoryTheory.End B) (a' : O →+* CategoryTheory.End C)

/-- A rational isomorphism of the full extended actions has actual integral
representatives exactly intertwining every order element in both directions. -/
def integralActionRationalIsoData
    (e : RationalAlgebraAction.of B (integralActionRationalExtension B b a) ≅
      RationalAlgebraAction.of C (integralActionRationalExtension C b a')) :
    EquivariantRationalIsoIntegralData a a' (RationalAlgebraAction.underlyingIso e) :=
  Rationalization.equivariantIntegralIsoData a a' b
    (RationalAlgebraAction.underlyingIso e) (by
      intro x
      change comp0 B B C (homToHom0 (a x)) (RationalAlgebraAction.hom0 e.hom) =
        comp0 B C C (RationalAlgebraAction.hom0 e.hom) (homToHom0 (a' x))
      have h := RationalAlgebraAction.intertwines e.hom (x : A)
      change comp0 B B C (integralActionRationalExtension B b a (x : A))
          (RationalAlgebraAction.hom0 e.hom) =
        comp0 B C C (RationalAlgebraAction.hom0 e.hom)
          (integralActionRationalExtension C b a' (x : A)) at h
      simpa only [integralActionRationalExtension_coe] using h)

end RationalExtension

end Langlands.AbelianScheme
