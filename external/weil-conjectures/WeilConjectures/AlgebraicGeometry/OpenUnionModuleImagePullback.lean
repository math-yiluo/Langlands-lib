/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.OpenUnionModuleImagePullbackCore

/-! # Sheaf gluing over an arbitrary open union

Source: Stacks Project, Tags 01EB and 08BV.
(blueprint: lem-pc-open-union-module-image-pullback).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- The direct-image restriction square for a union is a pullback, for any module sheaf.

Source: Stacks Project, Tag 01EB, lemma-mayer-vietoris, first sentence of its proof;
Tag 08BV, lemma-exact-sequence-j-star, displayed sequence.
(blueprint: lem-pc-open-union-module-image-pullback).

Proof: Fix a test open T. Conjugate each open image by the direct image of
`overFunctorEquiv`, identifying its sections with M(A ∩ T). The comparison
`schemeOpenModuleImage_section_restriction` identifies all four arrows with
ordinary restriction. The opens U ∩ T and V ∩ T have union (U ∪ V) ∩ T.
Sheaf gluing and separatedness give a unique section on that union for any
compatible pair. Uniqueness proves that amalgamation commutes with restriction
in T, addition, and multiplication by sections of the structure sheaf on T.
Thus amalgamation defines a morphism of module sheaves with the prescribed
composites. Separatedness proves uniqueness of this morphism. This is exactly
the pullback universal property. The same sheaf axiom covers empty and repeated
opens. No injectivity or complex is needed. -/
theorem schemeOpenUnionModuleImage_isPullback
    (X : Scheme.{u}) (U V : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    IsPullback
      ((schemeOpenModuleImageRestriction X
        (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M) := by
  apply schemeOpenUnionModuleImage_isPullback_of_sectionwise X U V M
  exact schemeOpenUnionModuleImage_sectionwise_gluing X U V M

end AlgebraicGeometry
