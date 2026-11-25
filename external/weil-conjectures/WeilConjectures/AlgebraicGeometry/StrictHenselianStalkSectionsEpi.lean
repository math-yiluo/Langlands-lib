/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.Functor.EpiMono
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsComparison
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-! # Local lifting of etale sections

Source: Stacks Project, Etale Cohomology, Tags 03Q6, 03QO and 09AX.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- At a strictly henselian point, stalkwise sections preserve epimorphisms.
Source: Stacks Project, Etale Cohomology, Tag 03Q6 (degree zero), Tag 03QO
(exactness of sections), and Tag 09AX (local-ring argument).
(blueprint: lem-weil-pbc-strict-henselian-stalk-sections-epi)

Proof: Write A for the strictly henselian local ring at x. The equality of the
underlying scheme functors identifies the scheme of i(top) with the top open
subscheme of X, hence with X. Its structural map to X may be a nonidentity
etale endomorphism; first restrict each sheaf to this etale object. Functoriality
of i and the faithfulness of the etale forgetful functor identify each i(U)
with the corresponding open of i(top), including every inclusion map.
The degree-zero continuity formula, restricted to cofinal affine neighbourhoods,
identifies stalkwise sections with sections on Spec A of the inverse image of
this restricted sheaf. This formula is natural in the sheaf and in the
neighbourhood inclusions. Restriction to an etale object and inverse image both
preserve epimorphisms. Sections on Spec A preserve epimorphisms: every etale
covering of its terminal object has a member with a point over the closed
point; strict henselianity gives a section over Spec A, so its covering sieve
contains the identity. An epimorphism of abelian sheaves is locally surjective,
hence surjective on this terminal object. Surjectivity is equivalent to being
an epimorphism in abelian groups. Transport this property through the natural
section comparison to etaleObjectStalkSections. This needs henselianity only
at x. Zero sheaves and a nonidentity structural map of i(top) cause no change.
No cohomology, injective resolution, or positive degree occurs in this statement. -/
theorem strictHenselian_stalkSections_preservesEpimorphisms
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (x : X) (hx : IsStrictlyHenselianLocalRing (X.presheaf.stalk x)) :
    (etaleObjectStalkSections X i x).PreservesEpimorphisms := by
  obtain ⟨H, hH, ⟨e⟩⟩ := strictHenselian_stalkSections_comparison i hi_inclusion x
  let := hH
  have : ((sheafSections (Spec (X.presheaf.stalk x)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 _)))).PreservesEpimorphisms := by
    let : IsStrictlyHenselianLocalRing (X.presheaf.stalk x) := hx
    refine ⟨?_⟩
    intro F G φ hφ
    exact (AddCommGrpCat.epi_iff_surjective _).2
      (Scheme.surjective_app_of_epi_of_isStrictlyHenselianLocalRing
        (X.presheaf.stalk x) φ)
  exact Functor.PreservesEpimorphisms.of_iso e.symm
