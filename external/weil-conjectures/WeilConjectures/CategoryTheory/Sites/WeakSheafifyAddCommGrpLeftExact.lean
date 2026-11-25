/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.LocallyBijectiveFiniteLimit
import Mathlib.CategoryTheory.Sites.Limits

/-! # Left exactness of existing abelian sheafification

Source: Stacks Project, Tag 00WJ and Tag 03CN.
(blueprint: lem-sc-weak-sheafify-addcommgrp-left-exact). -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An existing abelian sheafification whose inverted maps are exactly the locally
bijective maps is left exact, independently of the size of the site.

Source: Stacks Project, Tag 00WJ (left exactness of sheafification), applied to
abelian presheaves as in Tag 03CN, proof of the first assertion.
(blueprint: lem-sc-weak-sheafify-addcommgrp-left-exact)

Proof: finite limits of abelian presheaves are computed sectionwise. For a finite
category K and a diagram D, form the map from the limit of D to the limit of the
sheafified diagram, using the units of sheafification. This map is locally
bijective. For local surjectivity, lift the finitely many components of a section
on a common covering, and then refine that covering so that the finitely many
compatibility equations hold, using local injectivity of the units. For local
injectivity, refine the finitely many coverings on which two components agree.
The empty diagram gives the terminal presheaf, which is already a sheaf. Limits
of sheaves are computed as limits of their underlying presheaves, so the target
of this comparison is a sheaf. By the assumed characterization of inverted
maps, sheafifying the comparison is an isomorphism. The counit on its sheaf
target is also an isomorphism; hence the canonical finite-limit comparison of
the given left adjoint is an isomorphism. This proves preservation of every
finite limit. Together with the given right-adjoint instance for the inclusion,
this is exactly HasSheafify. No construction of larger-universe sheafification
or smallness of the site is used. -/
theorem hasSheafify_addCommGrp_of_weak
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    HasSheafify J AddCommGrpCat.{w} := by
  let S := presheafToSheaf J AddCommGrpCat.{w}
  let R := sheafToPresheaf J AddCommGrpCat.{w}
  have : PreservesFiniteLimits (S ⋙ R) := by
    constructor
    intro K _ _
    constructor
    intro D
    let α : D ⟶ D ⋙ (S ⋙ R) :=
      { app := fun k ↦ toSheafify J (D.obj k)
        naturality := fun _ _ f ↦ toSheafify_naturality J (D.map f) }
    have : ∀ k, Presheaf.IsLocallyInjective J (α.app k) := fun k ↦
      inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J (D.obj k)))
    have : ∀ k, Presheaf.IsLocallySurjective J (α.app k) := fun k ↦
      inferInstanceAs (Presheaf.IsLocallySurjective J (toSheafify J (D.obj k)))
    obtain ⟨hi, hs⟩ := Presheaf.locallyBijective_limMap J α
    have hf : J.W (limMap α) := (J.W_iff_isLocallyBijective _).2 ⟨hi, hs⟩
    have : IsIso (S.map (limMap α)) := (J.W_iff _).1 hf
    have : IsIso (sheafifyMap J (limMap α)) :=
      inferInstanceAs (IsIso (R.map (S.map (limMap α))))
    have ht : Presheaf.IsSheaf J (limit (D ⋙ (S ⋙ R))) :=
      Sheaf.isSheaf_of_isLimit (D ⋙ S) (limit.cone _) (limit.isLimit _)
    have : IsIso (toSheafify J (limit (D ⋙ (S ⋙ R)))) := isIso_toSheafify J ht
    have he : limit.post D (S ⋙ R) =
        sheafifyMap J (limMap α) ≫ inv (toSheafify J (limit (D ⋙ (S ⋙ R)))) := by
      apply sheafify_hom_ext _ _ _ ht
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
      apply limit.hom_ext
      intro k
      simp only [Category.assoc, limit.post_π, limMap_π]
      exact (toSheafify_naturality J (limit.π D k)).symm
    have : IsIso (limit.post D (S ⋙ R)) := by
      rw [he]
      infer_instance
    exact preservesLimit_of_isIso_post (S ⋙ R) D
  have : PreservesFiniteLimits S := preservesFiniteLimits_of_reflects_of_preserves S R
  exact HasSheafify.mk' J AddCommGrpCat.{w} (sheafificationAdjunction J AddCommGrpCat.{w})

end CategoryTheory
