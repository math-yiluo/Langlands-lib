/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.YonedaExtension.YonedaExtensionClass

/-! # Naturality of the concrete extension class

Source: Stacks Project, Tag 06XU, functoriality of the class construction.
(blueprint: lem-coef-yoneda-class-naturality)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u v w

namespace CategoryTheory.YonedaExtension

open Limits Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

private theorem normalized_naturality {V₀ U₀ V₁ U₁ V U V' U' : A} {n : ℕ}
    (α : Ext U₀ V₀ n) (β : Ext U₁ V₁ n)
    (l : V₀ ≅ V) (r : U₀ ≅ U) (l' : V₁ ≅ V') (r' : U₁ ≅ U')
    (p : V₀ ⟶ V₁) (q : U₀ ⟶ U₁)
    (h : α.comp (Ext.mk₀ p) (add_zero _) =
      (Ext.mk₀ q).comp β (zero_add _)) :
    (((Ext.mk₀ r.inv).comp α (zero_add _)).comp (Ext.mk₀ l.hom) (add_zero _)).comp
        (Ext.mk₀ (l.inv ≫ p ≫ l'.hom)) (add_zero _) =
      (Ext.mk₀ (r.inv ≫ q ≫ r'.hom)).comp
        (((Ext.mk₀ r'.inv).comp β (zero_add _)).comp
          (Ext.mk₀ l'.hom) (add_zero _)) (zero_add _) := by
  have hh := congrArg (fun x => (Ext.mk₀ r.inv).comp
    (x.comp (Ext.mk₀ l'.hom) (add_zero _)) (zero_add _)) h
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh

end CategoryTheory.YonedaExtension
