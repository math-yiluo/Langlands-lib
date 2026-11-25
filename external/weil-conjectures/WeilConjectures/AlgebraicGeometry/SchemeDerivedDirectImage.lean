/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-!
# Derived direct image on schemes

Source: the Weil conjectures blueprint, sec-picard-framework/det-thm-picard-coherence,
node lemma-coherent-base-change-invertible-sheaves; Stacks Project, Tag 0A1G, with the ringed-space
construction of Tag 079V (blueprint: lemma-coherent-base-change-invertible-sheaves).

## Main definitions

* `schemeDerivedDirectImage` specializes the ringed-space derived direct image to schemes.
* `schemeHigherDirectImage` takes its cohomology sheaf in any integer degree.
* `schemeModuleHigherDirectImage` first places a module in degree zero.
-/

@[expose] public section

universe u wX wS

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

/-- The unbounded derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_S)` is the ringed-space
construction for the underlying ringed-space morphism. Its K-injective computation is
supplied by `RingedSpace.derivedModuleDirectImage_computed_by_resolution`.
Source: blueprint sec-picard-framework/det-thm-picard-coherence, node
 lemma-coherent-base-change-invertible-sheaves; Stacks, Tags 0A1G and 079V
(blueprint: lemma-coherent-base-change-invertible-sheaves). -/
abbrev schemeDerivedDirectImage (f : X ⟶ S) :
    schemeDerivedCategory X ⥤ schemeDerivedCategory S :=
  RingedSpace.derivedModuleDirectImage f.toLRSHom.toShHom

/-- The higher direct image of a derived object in integer degree `i` is `H^i(Rf_*E)`,
a sheaf of `𝒪_S`-modules. Source: blueprint sec-picard-framework/det-thm-picard-coherence,
node lemma-coherent-base-change-invertible-sheaves; Stacks, Tag 0A1G
(blueprint: lemma-coherent-base-change-invertible-sheaves). -/
def schemeHigherDirectImage (f : X ⟶ S) (i : ℤ) :
    schemeDerivedCategory X ⥤ SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
  schemeDerivedDirectImage f ⋙
    DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i

/-- For an `𝒪_X`-module, higher direct image means higher direct image of that module
viewed as a complex in degree zero. Source: blueprint
sec-picard-framework/det-thm-picard-coherence, node lemma-coherent-base-change-invertible-sheaves;
Stacks, Tag 0A1G (blueprint: lemma-coherent-base-change-invertible-sheaves). -/
def schemeModuleHigherDirectImage (f : X ⟶ S) (i : ℤ) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
  DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0 ⋙
    schemeHigherDirectImage f i

end AlgebraicGeometry
