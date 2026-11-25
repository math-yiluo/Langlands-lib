/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CechResolutionDoubleComplex
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.InjectiveResolutionCohomologyPresheafData

/-!
# The cohomology presheaf computed by an injective resolution

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 2, evaluation comparison.
-/

@[expose] public section

universe u v

namespace CategoryTheory

/-- Evaluation of an injective resolution computes the Ext cohomology presheaf,
naturally in the object of the site.

Source: blueprint lemma-coherent-base-change-invertible-sheaves--1, Step 2; lem-sc-cech-spectral,
Step 1. Proof: for V in C, the sheafification adjunction, the free abelian group adjunction,
and Yoneda identify Hom from the sheafification of the free abelian representable
of V into any abelian sheaf G with G(V), as abelian groups. This identification is
natural in G and V, so it identifies the Hom complex of the injective resolution
with its evaluation complex at V. Computing Ext using this injective resolution
identifies the homology of that Hom complex with Ext from the free representable
to F. The Ext comparison is natural in the first argument, so the objectwise
isomorphisms commute with all restriction maps V' → V. Assemble them into the
claimed natural isomorphism. In degree zero this is the usual identification of
Hom from the free representable with sections. No covering family is involved.
(blueprint: lem-sc-injective-resolution-cohomology-presheaf) -/
theorem Sheaf.injectiveResolution_cohomologyPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (q : ℕ) :
    Nonempty
      ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).asFunctor ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q ≅
      F.cohomologyPresheaf q) := by
  obtain ⟨e, he⟩ := Sheaf.injectiveResolution_cohomologyPresheaf_data I q
  exact ⟨NatIso.ofComponents e he⟩

end CategoryTheory
