/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface

/-! # Small Ext with the canonical sheaf abelian structures
Source: the coefficient conventions in the diagonal tower proof.
(blueprint: lem-sfb-canonical-sheaf-ext). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- Small Ext for module sheaves, with the diagonal interface's canonical
abelian structure fixed in this theorem's type.
Source: the canonical coefficient categories in the diagonal tower proof
(blueprint: lem-sfb-canonical-sheaf-ext).
Proof: the existing small-Ext theorem for pro-etale module sheaves applies;
the named canonical abelian structure has exactly the same operations. -/
theorem kummerModuleHasExt (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} R)) := by
  exact geoCartierModuleExt R W

/-- Small Ext for abelian sheaves, with the diagonal interface's canonical
abelian structure fixed in this theorem's type.
Source: the canonical coefficient categories in the diagonal tower proof
(blueprint: lem-sfb-canonical-sheaf-ext).
Proof: use existing pro-etale integral small Ext. Naming the proof with the
canonical abelian structure shares its type without changing that category. -/
theorem kummerAbHasExt (W : Scheme.{u}) : HasExt.{u + 1} (DiagonalAb W) := by
  exact geoCartierIntegralExt W

end AlgebraicGeometry.ProEtale
