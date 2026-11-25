/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientRealizationIsoLift

/-! # Homology-level lift from a constant adic quotient realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- A realized isomorphism on a nonempty etale chart admits an algebraic
morphism whose cohomology maps are all isomorphisms.

Source: Stacks Project, sites-modules.tex, Tags 093J and 03DH; proetale.tex,
Tag 03Q3.
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-homology-lift).

Proof: apply the point-stalk extraction theorem to obtain an algebraic
isomorphism.  The unbounded derived isomorphism criterion identifies an
isomorphism in the derived category with isomorphisms on every homology object.
-/
theorem constantAdicQuotientRealization_homology_lift
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (W : Y.Etale) (_w : W.left)
    (E F : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (h : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj F)) :
    ∃ f : E ⟶ F, ∀ i : ℤ,
      IsIso ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) i).map f) := by
  obtain ⟨f, hf⟩ := constantAdicQuotientRealization_iso_lift X Y g d n W _w E F h
  refine ⟨f, ?_⟩
  exact (DerivedCategory.isIso_iff
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) f).mp hf

end AlgebraicGeometry.Scheme
