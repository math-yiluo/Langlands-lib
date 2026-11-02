import Langlands.AbelianScheme.RelativeIntegralActions
import Langlands.AbelianScheme.RationalAlgebraActionClasses
import Langlands.Algebra.IntegralOrderExtension

/-! # Actual comparison of relative integral restriction and ordinary pullback -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Module

universe u uI uA

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} (B : AbelianScheme S)
    {T T' : Over S}

/-- The actual abelian-scheme comparison underlying canonical relative restriction. -/
def relativeBaseChangeComparisonIso (f : T' ⟶ T) :
    (baseChange T'.hom).obj B ≅ (baseChange f.left).obj ((baseChange T.hom).obj B) where
  hom := Additive.ofMul
    (Langlands.GroupScheme.Cartier.baseChangeCompIso B.toCommGroupScheme f).hom
  inv := Additive.ofMul
    (Langlands.GroupScheme.Cartier.baseChangeCompIso B.toCommGroupScheme f).inv
  hom_inv_id := congrArg Additive.ofMul
    (Langlands.GroupScheme.Cartier.baseChangeCompIso B.toCommGroupScheme f).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul
    (Langlands.GroupScheme.Cartier.baseChangeCompIso B.toCommGroupScheme f).inv_hom_id

/-- Relative restriction is ordinary pullback conjugated by the actual comparison. -/
theorem relativeEndRestrict_eq_comparison (f : T' ⟶ T)
    (v : CategoryTheory.End ((baseChange T.hom).obj B)) :
    relativeEndRestrict B f v =
      (relativeBaseChangeComparisonIso B f).hom ≫ (baseChange f.left).map v ≫
        (relativeBaseChangeComparisonIso B f).inv := rfl

/-- The comparison intertwines relative restriction with ordinary pullback. -/
theorem relativeEndRestrict_comparison_intertwines (f : T' ⟶ T)
    (v : CategoryTheory.End ((baseChange T.hom).obj B)) :
    relativeEndRestrict B f v ≫ (relativeBaseChangeComparisonIso B f).hom =
      (relativeBaseChangeComparisonIso B f).hom ≫ (baseChange f.left).map v := by
  rw [relativeEndRestrict_eq_comparison]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

section RationalExtension

variable {I : Type uI} {A : Type uA} [Ring A] [Algebra ℚ A]
    {O : Subalgebra ℤ A} [Submodule.IsLattice ℚ O.toSubmodule]
    (b : Basis I ℤ O)

/-- Rationalize an actual integral action and extend from its full integer order. -/
def integralActionRationalExtension (a : O →+* CategoryTheory.End B) :
    A →ₐ[ℚ] End0 B :=
  IntegralOrderExtension.extend b ((Rationalization.ofEnd B).comp a)

@[simp]
theorem integralActionRationalExtension_coe
    (a : O →+* CategoryTheory.End B) (x : O) :
    integralActionRationalExtension B b a (x : A) = homToHom0 (a x) :=
  IntegralOrderExtension.extend_coe b _ x

/-- An actual intertwiner remains an intertwiner for the full rational extensions. -/
theorem integralActionRationalExtension_intertwines
    {B C : AbelianScheme S}
    (a : O →+* CategoryTheory.End B) (a' : O →+* CategoryTheory.End C)
    (v : B ⟶ C) (hv : ∀ x : O, a x ≫ v = v ≫ a' x) (x : A) :
    comp0 B B C (integralActionRationalExtension B b a x) (homToHom0 v) =
      comp0 B C C (homToHom0 v) (integralActionRationalExtension C b a' x) := by
  let L : A →ₗ[ℚ] Hom0 B C :=
    ((comp0 B B C).flip (homToHom0 v)).comp
      (integralActionRationalExtension B b a).toLinearMap
  let R : A →ₗ[ℚ] Hom0 B C :=
    ((comp0 B C C) (homToHom0 v)).comp
      (integralActionRationalExtension C b a').toLinearMap
  have eqMaps : L = R := by
    apply (b.extendOfIsLattice (M := O.toSubmodule) ℚ).ext
    intro k
    change comp0 B B C
        (integralActionRationalExtension B b a
          (b.extendOfIsLattice (M := O.toSubmodule) ℚ k)) (homToHom0 v) =
      comp0 B C C (homToHom0 v)
        (integralActionRationalExtension C b a'
          (b.extendOfIsLattice (M := O.toSubmodule) ℚ k))
    simp only [Basis.extendOfIsLattice_apply, integralActionRationalExtension_coe,
      comp0_homToHom0]
    exact congrArg (fun f : B ⟶ C => homToHom0 f) (hv (b k))
  exact DFunLike.congr_fun eqMaps x

/-- Rational extension of an integral action commutes with actual scheme pullback. -/
theorem integralActionRationalExtension_baseChange {S' : Scheme.{u}} (c : S' ⟶ S)
    (a : O →+* CategoryTheory.End B) :
    integralActionRationalExtension ((baseChange c).obj B) b (baseChangeOrderAction c B a) =
      (rationalBaseChangeEnd c B).comp (integralActionRationalExtension B b a) := by
  apply IntegralOrderExtension.algHom_ext b
  intro x
  simp only [integralActionRationalExtension_coe, AlgHom.comp_apply,
    baseChangeOrderAction_apply]
  exact (rationalBaseChangeHom_ofHom c (a x)).symm

/-- The direct and successive action families are equivariantly rationally isomorphic. -/
def relativeIntegralActionRationalComparisonIso (f : T' ⟶ T)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) :
    RationalAlgebraAction.of ((baseChange T'.hom).obj B)
        (integralActionRationalExtension ((baseChange T'.hom).obj B) b
          ((relativeEndRestrict B f).comp a)) ≅
      (RationalAlgebraAction.pullback f.left).obj
        (RationalAlgebraAction.of ((baseChange T.hom).obj B)
          (integralActionRationalExtension ((baseChange T.hom).obj B) b a)) := by
  refine RationalAlgebraAction.isoMk
    (Rationalization.inclusion.mapIso (relativeBaseChangeComparisonIso B f)) ?_
  intro x
  change comp0 _ _ _
      (integralActionRationalExtension ((baseChange T'.hom).obj B) b
        ((relativeEndRestrict B f).comp a) x)
      (homToHom0 (relativeBaseChangeComparisonIso B f).hom) =
    comp0 _ _ _ (homToHom0 (relativeBaseChangeComparisonIso B f).hom)
      (((rationalBaseChangeEnd f.left ((baseChange T.hom).obj B)).comp
        (integralActionRationalExtension ((baseChange T.hom).obj B) b a)) x)
  rw [← integralActionRationalExtension_baseChange]
  exact integralActionRationalExtension_intertwines b
    ((relativeEndRestrict B f).comp a)
    (baseChangeOrderAction f.left ((baseChange T.hom).obj B) a)
    (relativeBaseChangeComparisonIso B f).hom
    (fun y => relativeEndRestrict_comparison_intertwines B f (a y)) x

/-- Equality is in the published quotient by actual equivariant rational isomorphisms. -/
theorem relativeIntegralActionRationalComparison_classOf (f : T' ⟶ T)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) :
    RationalAlgebraAction.classOf
        (RationalAlgebraAction.of ((baseChange T'.hom).obj B)
          (integralActionRationalExtension ((baseChange T'.hom).obj B) b
            ((relativeEndRestrict B f).comp a))) =
      RationalAlgebraAction.pullbackClass f.left
        (RationalAlgebraAction.classOf
          (RationalAlgebraAction.of ((baseChange T.hom).obj B)
            (integralActionRationalExtension ((baseChange T.hom).obj B) b a))) :=
  RationalAlgebraAction.classOf_eq_iff.mpr
    ⟨relativeIntegralActionRationalComparisonIso B b f a⟩

end RationalExtension

end Langlands.AbelianScheme
