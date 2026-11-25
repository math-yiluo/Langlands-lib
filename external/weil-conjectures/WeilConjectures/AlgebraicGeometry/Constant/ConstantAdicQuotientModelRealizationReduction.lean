/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientRealizationScalarReduction
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientRealizationTowerTransition

/-! # Reduction of the consecutive realization comparison to the lower tower level

This is the geometric transport part of the consecutive quotient argument.  It
records the comparison before the supplied lower model is used; the latter is
then only a categorical cancellation in the parent theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- The realization of the scalar extension of the upper model reduces to the
lower level of the adic tower.

Source: Stacks Project, proetale.tex, Tag 09C6, consecutive quotient balancing;
Tags 0D6D and 03Q3 for the constant scalar comparison.
(blueprint: lem-weil-pbc-constant-adic-quotient-model-realization-reduction).

Proof: pull the normalization isomorphism of the supplied adic tower from the
upper quotient to the lower quotient along the pointed etale chart.  Paste it
with the canonical quotient scalar comparison and with the realization/scalar
extension comparison.  The supplied upper model isomorphism transports the
resulting comparison to the displayed lower realization.  Completion
evaluation commutes with the quotient projections, so all maps are over the
actual coefficient rings. -/
theorem constantAdicQuotient_model_realization_reduction
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (n : ℕ) (W : Y.Etale) (_w : W.left)
    (E' : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1))))
    (e' : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d (n + 1)).obj E' ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op (n + 1)))).obj (M.level (n + 1)))) :
    Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj
      ((CategoryTheory.ConstantScalarRealization.moduleDerivedExtension
        (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (I := d.ideal.map
            (algebraMap A (AdicCompletion d.ideal A)))
            (Nat.le_succ (n + 1))))).obj E') ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op n))).obj (M.level n)) := by
  rcases constantAdicQuotient_realization_scalar_reduction X Y g d n W _w E' with
    ⟨hscalar⟩
  rcases adicTowerPullback_consecutive_transition_iso X Y g d M n W _w with
    ⟨htower⟩
  rcases e' with ⟨e'⟩
  exact ⟨hscalar ≪≫
    Functor.mapIso (pbcDerivedExtend ((adicTowerInverseImage (W.hom ≫ g)).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))) e' ≪≫ htower⟩

end AlgebraicGeometry.Scheme
