/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.Condensed.ProfiniteActionEquivalence
public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSitePresentation
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Internal condensed actions form a Grothendieck abelian category

Source: paragraph (3) of the direct-image stability proof, action-site presentation
(blueprint: def-sfb-condensed-derived-invariants).

Through `siteEquivalence`, internal actions of a topological group `G` on internal modules
over a condensed ring `A` are equivariant sheaves on the small profinite site, which the
action-site presentation identifies with modules over the twisted ringed site. We deduce
that the action category is abelian and Grothendieck, and that forgetting the action is
exact and detects exactness.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar.ActionSite

variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The action-site presentation on the small profinite site. -/
theorem presentation_nonempty :
    Nonempty (InternalActionSite.Presentation (groupPresheaf G) modelPrecoverage
      modelPrecoverage_isSiteForCoverings (ringSheaf A)) :=
  InternalActionSite.presentation (groupPresheaf G) modelPrecoverage
    modelPrecoverage_isSiteForCoverings (groupPresheaf_isSheaf G) (ringSheaf A)

/-- The category of internal actions is abelian, for its given additive structure. -/
theorem actionAbelian_nonempty : Nonempty (ActionAbelian A G) := by
  obtain ⟨P⟩ := presentation_nonempty A G
  let E := (siteEquivalence A G).trans P.sheafEquivalence
  have : HasFiniteProducts (Equivariant A G) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.functor⟩
  let ab : Abelian (Equivariant A G) := abelianOfEquivalence E.functor
  exact ⟨{ normalMono := ab.toIsNormalMonoCategory
           normalEpi := ab.toIsNormalEpiCategory
           products := ab.has_finite_products
           kernels := ab.has_kernels
           cokernels := ab.has_cokernels }⟩

/-- The category of internal actions is Grothendieck abelian, for any of its abelian
structures. -/
theorem isGrothendieckAbelian [ActionAbelian A G] :
    IsGrothendieckAbelian.{u + 1} (Equivariant A G) := by
  obtain ⟨P⟩ := presentation_nonempty A G
  have := SheafOfModules.isGrothendieckAbelian
    (InternalActionSite.twistedRing (groupPresheaf G) modelPrecoverage
      modelPrecoverage_isSiteForCoverings (ringSheaf A))
  exact IsGrothendieckAbelian.of_equivalence ((siteEquivalence A G).trans P.sheafEquivalence).symm

variable {A G}

/-- Forgetting the action is faithful. -/
instance forgetAction_faithful : (forgetAction (A := A) (G := G)).Faithful where
  map_injective h := Subtype.ext h

/-- Forgetting the action preserves kernels. -/
theorem forgetAction_preservesKernel {X Y : Equivariant A G} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) (forgetAction (A := A) (G := G)) := by
  obtain ⟨P⟩ := presentation_nonempty A G
  let F := InternalActionSite.forgetSheaf (K := groupPresheaf G)
    modelPrecoverage.toGrothendieck (siteRing A)
  obtain ⟨_⟩ := P.createsKernels _ _ (toSite.map f)
  have : PreservesLimit (parallelPair (toSite.map f) 0) F :=
    preservesLimit_of_createsLimit_and_hasLimit _ _
  have : PreservesLimit (parallelPair f 0 ⋙ toSite) F :=
    preservesLimit_of_iso_diagram (K₁ := parallelPair (toSite.map f) 0) F
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp))
  have : PreservesLimit (parallelPair f 0) (forgetAction ⋙ toSiteModule A) :=
    preservesLimit_of_natIso _ (toSiteForgetIso A)
  exact preservesLimit_of_reflects_of_preserves _ (toSiteModule A)

/-- Forgetting the action preserves cokernels. -/
theorem forgetAction_preservesCokernel {X Y : Equivariant A G} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) (forgetAction (A := A) (G := G)) := by
  obtain ⟨P⟩ := presentation_nonempty A G
  let F := InternalActionSite.forgetSheaf (K := groupPresheaf G)
    modelPrecoverage.toGrothendieck (siteRing A)
  obtain ⟨_⟩ := P.createsCokernels _ _ (toSite.map f)
  have : PreservesColimit (parallelPair (toSite.map f) 0) F :=
    preservesColimit_of_createsColimit_and_hasColimit _ _
  have : PreservesColimit (parallelPair f 0 ⋙ toSite) F :=
    preservesColimit_of_iso_diagram (K₁ := parallelPair (toSite.map f) 0) F
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp))
  have : PreservesColimit (parallelPair f 0) (forgetAction ⋙ toSiteModule A) :=
    preservesColimit_of_natIso _ (toSiteForgetIso A)
  exact preservesColimit_of_reflects_of_preserves _ (toSiteModule A)

variable (A G)

/-- Forgetting the action is exact and detects exactness of short complexes. -/
theorem forgetAction_exact [ActionAbelian A G] :
    PreservesFiniteLimits (forgetAction (A := A) (G := G)) ∧
    PreservesFiniteColimits (forgetAction (A := A) (G := G)) ∧
    (∀ S : ShortComplex (Equivariant A G),
      S.Exact ↔ (S.map (forgetAction (A := A) (G := G))).Exact) := by
  have {X Y : Equivariant A G} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0)
      (forgetAction (A := A) (G := G)) := forgetAction_preservesKernel f
  have {X Y : Equivariant A G} (f : X ⟶ Y) : PreservesColimit (parallelPair f 0)
      (forgetAction (A := A) (G := G)) := forgetAction_preservesCokernel f
  have : (forgetAction (A := A) (G := G)).PreservesHomology := {}
  refine ⟨Functor.preservesFiniteLimits_of_preservesKernels _,
    Functor.preservesFiniteColimits_of_preservesCokernels _, fun S ↦ ?_⟩
  exact (ShortComplex.exact_map_iff_of_faithful S _).symm

end CategoryTheory.CondensedBar.ActionSite
