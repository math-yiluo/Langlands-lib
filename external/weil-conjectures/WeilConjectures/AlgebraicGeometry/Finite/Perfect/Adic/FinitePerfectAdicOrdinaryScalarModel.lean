/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarComponents
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarCompatibility

/-! # Ordinary scalar comparison for constant quotient modules

Source: Stacks Project, Tags 093J, 093M, 03CY and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

/-- Ordinary constant quotient modules agree with completed extension, compatibly with
consecutive coefficient restriction. This is an assertion in abelian categories only.

Source: Stacks Project, Modules on Sites, Tags 093J and 093M; Tag 03CY for associated
module sheafification and Cohomology on Sites, Tag 06YY for scalar composition.
(blueprint: lem-weil-pbc-finite-perfect-adic-ordinary-scalar-model).

Proof: first use the rank-one quotient comparison and its consecutive compatibility,
then extend the square to arbitrary quotient modules by exactness, coproducts and a
finite free presentation.  No derived category, algebraic tower, or perfectness
assumption is used.  Zero rings, zero modules and empty charts are covered by the
same exact functor argument.
-/
theorem finitePerfectAdicOrdinaryScalar_model
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) :
    ∃ e : ∀ n : ℕ, finitePerfectAdicOrdinaryScalarSource X d V U W f n ≅
        finitePerfectAdicOrdinaryScalarTarget X d W n,
      ∀ (n : ℕ) (N : ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))),
        (e (n + 1)).hom.app
            ((ModuleCat.restrictScalars
              (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj N) ≫
          (finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom.app N =
        (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom.app N ≫
          (e n).hom.app N := by
  obtain ⟨e, hunit⟩ := finitePerfectAdicOrdinaryScalar_components X d V U W f
  exact ⟨e, finitePerfectAdicOrdinaryScalar_compatibility X d V U W f e hunit⟩

end AlgebraicGeometry.Scheme
