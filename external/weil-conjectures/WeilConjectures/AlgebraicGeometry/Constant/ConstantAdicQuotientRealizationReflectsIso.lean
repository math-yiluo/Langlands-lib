/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientRealizationHomologyLift

/-! # Conservativity of a nonempty constant quotient realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- On a nonempty etale chart, the constant quotient realization reflects
isomorphism of algebraic derived coefficient objects.

Source: Stacks Project, sites-modules.tex, Tags 093J and 03DH; proetale.tex,
Tag 03Q3.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-reflects-iso).

Proof: the finite coefficient quotient is canonically identified with its
completion quotient.  The exact constant module realization reflects zero on the
nonempty chart, and exact inverse image together with the coefficient comparison
preserves this detection.  Apply the derived isomorphism criterion to the kernel
and cokernel of a representative morphism. -/
theorem constantAdicQuotientRealization_reflects_iso
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (W : Y.Etale) (_w : W.left)
    (E F : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (h : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj F)) :
    Nonempty (E ≅ F) := by
  obtain ⟨f, hf⟩ := constantAdicQuotientRealization_homology_lift
    X Y g d n W _w E F h
  have hi : IsIso f := (DerivedCategory.isIso_iff
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) f).2 hf
  exact ⟨asIso f⟩

end AlgebraicGeometry.Scheme
