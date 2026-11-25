/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleExtContinuityFinite
/-! Algebraic-closure coefficient Ext continuity from finite coefficient continuity.
Source: blueprint `lemma-continuity-ext-out-constructible-complex--1`, clause (1), using the
finite-subextension presentation of the algebraic closure.
(blueprint: lem-finite-window-ind-ext-bound-algcl-continuity)
The coefficient descent and transport of filtered derived-Hom factorizations
remain to be formalized.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
theorem padicAlgCl_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [MonObj (Profinite.padicAlgClRingObj ℓ)]
    [IsCommMonObj (Profinite.padicAlgClRingObj ℓ)]
    (hfinite : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      @ConstantModelExtContinuity (Profinite.continuousMapRingObj E) _ _ X) :
    ConstantModelExtContinuity (Profinite.padicAlgClRingObj ℓ) X := by
  sorry
end AlgebraicGeometry.ProEtale
