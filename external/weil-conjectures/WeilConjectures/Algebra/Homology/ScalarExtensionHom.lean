/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive

/-! # Scalar extension of maps between base-extended complexes

Source: Stacks Project, Derived Categories of Schemes, Tag 09RE, affine proof;
Mathlib's `ModuleCat.extendScalarsComp`
(blueprint: def-pc-complex-scalar-extension-hom).
-/

@[expose] public section

universe u₁

open CategoryTheory

namespace CochainComplex

/-- Extend a chain map over `S` between complexes extended from `R` to `T`, transporting
along the canonical associativity of extension of scalars and the equality `h = g.comp f`.
Source: Stacks Project, Derived Categories of Schemes, Tag 09RE, affine proof
(blueprint: def-pc-complex-scalar-extension-hom). -/
noncomputable def scalarExtensionHom
    {R S T : Type u₁} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hc : h = g.comp f)
    (P Q : CochainComplex (ModuleCat.{u₁} R) ℤ)
    (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q) :
    ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj Q :=
  eqToHom (congrArg (fun t ↦
      ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj P) hc) ≫
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).hom.app P ≫
    ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).map a ≫
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).inv.app Q ≫
    eqToHom (congrArg (fun t ↦
      ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj Q) hc.symm)

end CochainComplex
