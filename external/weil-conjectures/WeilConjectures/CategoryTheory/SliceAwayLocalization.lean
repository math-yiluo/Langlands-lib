/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Sectionwise localization on a slice site

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af, displayed resolution
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u vC uC

open CategoryTheory Opposite

namespace CategoryTheory

/-- A presheaf of modules with coherent coordinates in the sectionwise localizations.
The restriction rule is imposed on all fractions, which exhaust every localization; hence
this specifies the presheaf up to a unique coordinate-preserving isomorphism. This structure
contains actual presheaf data, rather than selecting data from an existence assertion.
Source: Stacks Project, Tag 0997, lemma-hom-from-Af, displayed resolution on the slice.
(auxiliary; not a blueprint node). -/
structure SliceAwayLocalization {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U)) where
  /-- The underlying presheaf on the slice. -/
  val : PresheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).over U).obj
  /-- Sectionwise linear coordinates in the ordinary localization. -/
  equiv (V : (Over U)ᵒᵖ) :
    val.obj V ≃ₗ[O.obj.obj (op V.unop.left)]
      Localization.Away (O.obj.map V.unop.hom.op f)
  /-- Restriction sends a fraction to the fraction of the restricted numerator. -/
  restriction {V W : (Over U)ᵒᵖ} (g : V ⟶ W)
      (a : O.obj.obj (op V.unop.left)) (n : ℕ) :
    equiv W (val.map g ((equiv V).symm
      (algebraMap _ _ a * IsLocalization.Away.invSelf
        (O.obj.map V.unop.hom.op f) ^ n))) =
      algebraMap _ _ (O.obj.map g.unop.left.op a) *
        IsLocalization.Away.invSelf (O.obj.map W.unop.hom.op f) ^ n

end CategoryTheory
