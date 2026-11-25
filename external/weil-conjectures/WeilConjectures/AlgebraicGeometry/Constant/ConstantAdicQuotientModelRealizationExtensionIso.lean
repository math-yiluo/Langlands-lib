/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientModelRealizationReduction

/-! # Realization-level extension comparison for consecutive quotient models

This is the geometric transport step in the algebraic extension argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- The consecutive tower normalization transports supplied constant models after
inverse image and identifies the lower realization with derived scalar extension of
the upper model.

Source: Stacks Project, proetale.tex, Tag 09C6, consecutive quotient balancing;
Tags 0D6D and 03Q3.
(blueprint: lem-weil-pbc-constant-adic-quotient-model-realization-extension-iso).

Proof: apply the normalization of the supplied adic tower at the consecutive
indices, pull it back to the pointed etale chart, and paste the tensor-pullback
comparison with the canonical constant quotient scalar comparison.  The two supplied
model isomorphisms then identify the resulting endpoints.  Completion evaluation
commutes with the quotient projections by the canonical factor maps. -/
theorem constantAdicQuotient_model_realization_extension_iso
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
    Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj
      ((CategoryTheory.ConstantScalarRealization.moduleDerivedExtension
        (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := d.ideal.map
            (algebraMap A (AdicCompletion d.ideal A)))
            (Nat.le_succ (n + 1))))).obj E') ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E) := by
  rcases constantAdicQuotient_model_realization_reduction X Y g d M n W _w E' e' with
    ⟨hred⟩
  rcases e with ⟨e⟩
  exact ⟨hred ≪≫ e.symm⟩

end AlgebraicGeometry.Scheme
