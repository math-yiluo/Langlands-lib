/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage

/-! # Surjectivity of the finite étale image with fixed endpoints -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mk₀
  Ext.mk₀CompMk₀ Ext.mapExactFunctor comparisonUpperStar

/-- Every pro-etale coefficient Ext class has an étale representative with fixed endpoints.
Source: exact site-comparison Ext bijectivity, with canonical endpoint isomorphisms.
(blueprint: lem-sfb-diagonal-trace-finite-etale-image-surjective).

Proof: exact site comparison gives a bijection on Ext. Its composition with the explicit
endpoint-transport equivalence is an equivalence, so its forward map is surjective. -/
theorem finiteEtaleProImage_surjective (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) :
    Function.Surjective (finiteEtaleProImage A T N hA) := by
  unfold finiteEtaleProImage
  exact (finiteEtaleProEquiv A T N hA).surjective

/-- The equivalence-based finite image has the usual exact-functor formula.
Source: definitions of comparison and endpoint transport.
(blueprint: lem-sfb-diagonal-trace-finite-etale-image-surjective). -/
theorem finiteEtaleProImage_apply (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0)
    (b : Ext (Etale.ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2) :
    finiteEtaleProImage A T N hA b =
      Ext.mk₀CompMk₀ (finiteEtaleConstantIso A T).inv
        (b.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) T))
        (finiteEtaleLineIso A T N hA).hom := by
  unfold finiteEtaleProImage finiteEtaleProEquiv finiteEtaleRawEquiv
  rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
