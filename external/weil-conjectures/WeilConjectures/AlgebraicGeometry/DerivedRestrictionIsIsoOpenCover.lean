/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- Derived restriction detects isomorphisms on a two-member open cover.
Source: Stacks Project, Tag 08DF, the local cohomology criterion in its proof;
Mathlib `DerivedCategory.isIso_iff` and sheaf locality (Tag 04TN).
(blueprint: lem-pc-derived-restriction-isIso-open-cover).

Proof: An isomorphism is detected by all homology functors. Exact restriction
commutes with homology, so the two local hypotheses make every homology map an
isomorphism on both opens. Sheaf-module isomorphisms are local on an open cover,
so every global homology map is invertible, and hence so is the derived map.
This also covers an empty member or an empty scheme. -/
theorem derived_restriction_isIso_open_cover (X : Scheme.{u}) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    {E F : schemeDerivedCategory X} (φ : E ⟶ F)
    (hU : IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.map φ))
    (hV : IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.map φ)) : IsIso φ := by
  apply (DerivedCategory.isIso_iff _ φ).2
  intro n
  let W : Bool → X.Opens := fun b ↦ if b then U else V
  have hW : ⨆ b, W b = ⊤ := by
    simpa [W, iSup_bool_eq] using hcover
  apply (sheaf_module_isIso_iff_isIso_over_open_cover
    X.toRingedSpace Bool W hW _ _ _).2
  intro b
  have hb : IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (W b)).mapDerivedCategory.map φ) := by
    cases b
    · exact hV
    · exact hU
  exact (NatIso.isIso_map_iff
    ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
      (W b)).mapDerivedCategoryHomologyFunctorIso n) φ).2 (by
        dsimp
        infer_instance)

end AlgebraicGeometry.Scheme
