/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import Mathlib.CategoryTheory.Functor.EpiMono
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsComparisonCore
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsComparisonIso

/-! # Degree-zero continuity for etale sections

Source: Stacks Project, Etale Cohomology, Tag 03Q6.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Stalkwise sections factor through inverse image to the local scheme and its
section functor. This comparison requires no henselianity.
Source: Stacks Project, Etale Cohomology, Tag 03Q6 (degree-zero continuity).
(blueprint: lem-weil-pbc-strict-henselian-stalk-sections-comparison)

Proof: Restrict the sheaf to the etale object i(top), then pull it back along the
canonical map from Spec of the local ring at x to its underlying scheme. The
underlying scheme of i(top) is identified with X by hi_inclusion. This composite
inverse-image functor H preserves epimorphisms, since both restriction to an
etale object and inverse image are left adjoints. Do not identify the structural
map of i(top) with the identity: it may be a nonidentity etale endomorphism.
Functoriality of i and faithfulness of the etale forgetful functor identify i(U)
with the corresponding open of i(top), compatibly with every inclusion map.
Choose one affine neighbourhood V of x in the underlying X and restrict
further to principal affine neighbourhoods inside V. These are cofinal in the
reverse-inclusion neighbourhood category, and their coordinate-ring colimit is
the stalk ring. Apply degree-zero continuity with base V (which is qcqs) and
the sheaf restricted to i(V). This identifies the colimit of their sections
with sections of the inverse-image sheaf on Spec of the stalk ring. Descent of
sections and of equalities gives respectively surjectivity and injectivity of this
comparison. These maps respect addition
and are natural in the sheaf. They therefore give the stated natural
isomorphism. All sheaves and section groups use the original coefficient
universe; no derived functor or cohomology-universe comparison is used. -/
theorem strictHenselian_stalkSections_comparison
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X) :
    ∃ H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
        Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1},
      H.PreservesEpimorphisms ∧
        Nonempty (etaleObjectStalkSections X i x ≅
          H ⋙ (sheafSections (Spec (X.presheaf.stalk x)).smallEtaleTopology
            AddCommGrpCat.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 _)))) := by
  obtain ⟨H, ⟨adj⟩⟩ := strictHenselian_stalkSections_comparison_functor (X.fromSpecStalk x)
  exact ⟨H, Functor.preservesEpimorphisms_of_adjunction adj,
    strictHenselian_stalkSections_comparison_iso i hi_inclusion x H adj⟩
