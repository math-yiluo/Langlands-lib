/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientModelRealizationExtensionIso
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientRealizationReflectsIso

/-! # Algebraic extension isomorphism for consecutive constant quotient models

This is the algebraic derived reduction extracted from the universal-reduction
statement.  The geometric comparison hypotheses remain explicit so that the
statement is strictly smaller than the Hom-bijection conclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- The supplied consecutive constant quotient models are related by derived
scalar extension along the canonical quotient map.

Source: Stacks Project, proetale.tex, Tag 09C6, consecutive quotient balancing;
Tags 0D6D and 03Q3 for constant scalar comparison and stalk detection.
(blueprint: lem-weil-pbc-constant-adic-quotient-model-extension-iso).

Proof: Apply the tower normalization after inverse image to the etale chart,
then use the tensor-pullback comparison and the supplied constant model
isomorphisms.  The canonical quotient maps commute with the completion
projections.  The constant realization scalar comparison identifies the
resulting geometric reduction with derived scalar extension of E'.  Passing to
a geometric stalk over the chosen point identifies this extension with E.
The nonempty point is needed for this stalk detection; no perfectness or
boundedness hypothesis is used. -/
theorem constantAdicQuotient_model_extension_iso
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (n : ℕ) (W : Y.Etale) (_w : W.left)
    (E' : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1))))
    (E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (e' : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d (n + 1)).obj E' ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op (n + 1)))).obj (M.level (n + 1))))
    (e : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op n))).obj (M.level n))) :
    Nonempty ((CategoryTheory.ConstantScalarRealization.moduleDerivedExtension
      (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := d.ideal.map
          (algebraMap A (AdicCompletion d.ideal A)))
          (Nat.le_succ (n + 1))))).obj E' ≅ E) := by
  let q := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := d.ideal.map
      (algebraMap A (AdicCompletion d.ideal A))) (Nat.le_succ (n + 1)))
  have hreal := constantAdicQuotient_model_realization_extension_iso
    X Y g d M n W _w E' E e' e
  exact constantAdicQuotientRealization_reflects_iso X Y g d n W _w
    ((CategoryTheory.ConstantScalarRealization.moduleDerivedExtension q).obj E') E
    hreal

end AlgebraicGeometry.Scheme
