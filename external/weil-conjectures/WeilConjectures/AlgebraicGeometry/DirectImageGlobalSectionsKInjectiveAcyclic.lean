/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
import WeilConjectures.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.GlobalSectionsPointUnitTransport

/-!
# Global-sections acyclicity of a direct image of a K-injective

Source: Stacks Project, Cohomology, Tags 079W and 0D5T; Duality, Tag 0B6I.
(blueprint: lem-pc-direct-image-global-sections-kinjective-acyclic).
-/

@[expose] public section

universe u w wA
open CategoryTheory Opposite
set_option autoImplicit false

namespace AlgebraicGeometry

/-- Direct image of a K-injective complex is acyclic for subsequent global sections.
No preservation of K-injectivity by direct image is asserted.
Source: Stacks Project, Cohomology, Tags 079W and 0D5T; Duality, Tag 0B6I.
(blueprint: lem-pc-direct-image-global-sections-kinjective-acyclic).

Proof: let p_Y be the morphism to the one-point ringed space with ring Γ(Y,O_Y).
Apply the successive-direct-image acyclicity statement
lem-pc-ringed-space-direct-image-kinjective-acyclic to f and p_Y, using the standard
model of the derived category on the point if needed. Modules on that point are
Γ(Y,O_Y)-modules, and evaluation on the point is an exact equivalence. The underived
identification of p_Y direct image followed by evaluation with global sections is
the identity on sections and their scalar action. Right-derived uniqueness transports
this identification and its units through the exact equivalence. Thus the unit for
global sections at f_*I is the image of the invertible unit for p_Y direct image at
f_*I, conjugated by the localization factorization isomorphisms. Functors preserve
isomorphisms, so the displayed unit is invertible. This works for unbounded I and
arbitrary f: acyclicity, rather than K-injectivity of f_*I, is what is transported. -/
theorem isIso_directImage_globalSections_unit_on_kInjective
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))]
    (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    IsIso ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
  let _ : HasDerivedCategory (SheafOfModules.{u} (moduleRings (globalSectionsPoint Y))) :=
    HasDerivedCategory.standard _
  apply globalSections_unit_isIso_of_point_unit f I
  exact RingedSpace.isIso_moduleDirectImage_unit_on_kInjective
    f.toLRSHom.toShHom (toGlobalSectionsPoint Y) I

end AlgebraicGeometry
