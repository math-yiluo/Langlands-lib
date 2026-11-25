/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import all WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # Finite local models for a locally free coefficient line

Source: Stacks Project, Tag 03RV; coefficient-twist blueprint, proof steps 1 and 8.
(blueprint: lem-pur-finite-locally-free-line-models)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

/-- A rank-one module over a finite constant coefficient ring is locally constant,
constructible, and has finite geometric stalks.

Source: Stacks Project, Tag 03RV; coefficient-twist blueprint, proof steps 1 and 8.
(blueprint: lem-pur-finite-locally-free-line-models)

Proof: the rank-one trivializing cover identifies the module on every chart with
its regular coefficient module. The constant-scalar comparison identifies these
with constant finite modules in the fixed-ring sheaf category. The proved finite
local-model theorem therefore supplies finite stalks and local constancy. The
trivial stratification witnesses fixed-ring constructibility; transport it back
through the constant-scalar constructibility equivalence. The equivalence uses a
positive identity stratum also on the empty scheme, and allows the zero ring. -/
theorem finiteLocallyFreeLine_models (S : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    IsLocallyConstantProEtaleModuleSheaf S A L ∧
      IsConstructibleProEtaleModuleSheaf S A L ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite (proEtaleGeometricModuleStalk s (proEtaleConstantRing S A) L) := by
  let := hL
  have hf := WeilConjectures.line_finite_models S A L
  obtain ⟨hl, hs⟩ := (finiteLocal_iff S A L).mp hf
  refine ⟨hl, (proEtaleModuleRestriction_constructible_iff S A L).mpr ?_, hs⟩
  refine ⟨Stratification.trivial S, fun _ ↦ ?_⟩
  exact ProEtale.isFiniteLocallyConstant_of_iso
    ((ProEtale.upperStarId _ S).app _).symm hf

end AlgebraicGeometry.Scheme
