/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenIntersectionMateIso

/-! # Invertible cross components of the open difference map

Source: Stacks Project, Tags 08DG and 08FE, restriction of the overlap counit.
(blueprint: lem-sc-derived-open-cross-components-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
-- Threefold transported overlap restrictions require additional instance search.
-- Transported threefold restrictions require the same instance budget as the parent theorem.
/-- The adjoint overlap counits are invertible on the opposite open. This concerns
only the individual summands, without choosing a difference diagram or a gluing object.
Source: Stacks Project, Cohomology, Tag 08DG (lemma-glue), the restriction of the
second arrow to U and V; Tag 08FE (lemma-restrict-direct-image).
(blueprint: lem-sc-derived-open-cross-components-iso).

Proof: apply `derived_open_intersection_mate_isIso` with O = U, P = V,
and W = U ∩ V to obtain invertibility of rU(b). For the other component let
f be the adjW-adjoint of eU.inv followed by sU of the U counit, with target
RjW_*(sU A). The same theorem with O = V and P = U proves invertibility
of rV(f), using commutativity of intersection. Naturality of adjW.homEquiv
in its target identifies a with f followed by RjW_*(c.hom). Restriction
preserves this composition and both factors are isomorphisms, so rV(a)
is invertible. The single-mate theorem accepts arbitrary adjunctions and
empty opens; no covering hypothesis or separate adjunction comparison is needed. -/
theorem derived_open_cross_components_isIso
    (X : Scheme.{u}) (U V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (c : (schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory.obj A ≅
      (schemeOpenOverlapRestriction X
        (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory.obj B)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjW : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι) :
    let rU := (schemeOpenRestriction X U).mapDerivedCategory;
    let rV := (schemeOpenRestriction X V).mapDerivedCategory;
    let sU := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory;
    let sV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory;
    let eU := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : U ⊓ V ⟶ U);
    let eV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : U ⊓ V ⟶ V);
    let AU := (schemeDerivedDirectImage U.ι).obj A;
    let BV := (schemeDerivedDirectImage V.ι).obj B;
    let a := adjW.homEquiv AU (sV.obj B)
      (eU.inv.app AU ≫ sU.map (adjU.counit.app A) ≫ c.hom);
    let b := adjW.homEquiv BV (sV.obj B)
      (eV.inv.app BV ≫ sV.map (adjV.counit.app B));
    IsIso (rU.map b) ∧ IsIso (rV.map a) := by
  dsimp only
  constructor
  · exact derived_open_intersection_mate_isIso X U V (U ⊓ V) rfl
      (homOfLE inf_le_right) adjV adjW B
  · let sU := (schemeOpenOverlapRestriction X
        (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory
    let eU := schemeDerivedOpenRestrictionCompIso X
      (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let f := adjW.homEquiv ((schemeDerivedDirectImage U.ι).obj A) (sU.obj A)
      (eU.inv.app _ ≫ sU.map (adjU.counit.app A))
    have hf : IsIso ((schemeOpenRestriction X V).mapDerivedCategory.map f) :=
      derived_open_intersection_mate_isIso X V U (U ⊓ V) (inf_comm U V)
        (homOfLE inf_le_left) adjU adjW A
    rw [← Category.assoc, adjW.homEquiv_naturality_right, Functor.map_comp]
    change IsIso ((schemeOpenRestriction X V).mapDerivedCategory.map f ≫
      (schemeOpenRestriction X V).mapDerivedCategory.map
        ((schemeDerivedDirectImage (U ⊓ V).ι).map c.hom))
    infer_instance

end AlgebraicGeometry
