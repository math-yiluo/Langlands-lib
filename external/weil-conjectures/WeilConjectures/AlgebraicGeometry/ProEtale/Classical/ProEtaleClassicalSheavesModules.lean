/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement

import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.AffinePresentationSectionColimit
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitMaps
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitFactorization
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Spectral.ConstructibleTopology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.RingTheory.IndEtaleSmallIndex
import WeilConjectures.RingTheory.ProEtale.Etale
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Classical pro-étale sheaves of modules

## References

* Stacks Project, Tags 099T, 04JC and 03DA

## Implementation details

Sheaves of modules use the fixed-coefficient `ModuleCat` encoding. The constant-ring action is
the unique extension of its discrete scalar actions through sheafification; comparison carries
those scalar actions along the same inclusion of sites. Classicality is the existing predicate
on the underlying sheaf of sets.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem comparisonForgetPreservesKan (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    (forget (ModuleCat.{u + 1} Λ)).PreservesLeftKanExtensions
      (Scheme.toProEt X).op := by
  intro P
  let : PreservesFilteredColimitsOfSize.{u, u + 1}
      (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
      (forget (ModuleCat.{u + 1} Λ)) P (Scheme.toProEt X).op V := by
    intro V
    infer_instance
  infer_instance

private noncomputable def comparisonForgetIso (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} Λ)) ≅
      sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ)) ⋙
        Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X) := by
  let := comparisonForgetPreservesKan X Λ
  exact sheafPullbackForgetIso X.smallEtaleTopology (Scheme.ProEt.topology X)
    (Scheme.toProEt X) (forget (ModuleCat.{u + 1} Λ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparisonForgetIso_counit (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (comparisonForgetIso X Λ).inv.app
        ((comparisonLowerStar (ModuleCat.{u + 1} Λ) X).obj G) ≫
      (sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} Λ))).map
        ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.app G) =
      (Scheme.proEtaleSiteComparison X).counit.app
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget (ModuleCat.{u + 1} Λ))).obj G) := by
  let := comparisonForgetPreservesKan X Λ
  let M := ModuleCat.{u + 1} Λ
  let V := sheafCompose X.smallEtaleTopology (forget M)
  let W := sheafCompose (Scheme.ProEt.topology X) (forget M)
  let R := comparisonLowerStar M X
  let Rs := (Scheme.toProEt X).sheafPushforwardContinuous
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  let adj := comparisonAdjunction M X
  let adjs := Scheme.proEtaleSiteComparison X
  let e := comparisonForgetIso X Λ
  have hu := sheafPullbackForgetIso_unit X.smallEtaleTopology
    (Scheme.ProEt.topology X) (Scheme.toProEt X) (forget M) (R.obj G)
  change V.map (adj.unit.app (R.obj G)) ≫ Rs.map (e.hom.app (R.obj G)) =
    adjs.unit.app (V.obj (R.obj G)) at hu
  have hu' : adjs.unit.app (V.obj (R.obj G)) ≫ Rs.map (e.inv.app (R.obj G)) =
      V.map (adj.unit.app (R.obj G)) := by
    rw [← hu, Category.assoc, ← Rs.map_comp, e.hom_inv_id_app, Rs.map_id]
    exact Category.comp_id _
  apply (adjs.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, hu']
  change V.map (adj.unit.app (R.obj G)) ≫ V.map (R.map (adj.counit.app G)) = _
  rw [← V.map_comp, adj.right_triangle_components]
  exact (V.map_id _).trans (adjs.right_triangle_components (W.obj G)).symm

/-- Comparison inverse image is exact and fully faithful on modules over any discrete
commutative ring, with essential image the classical module sheaves and restriction
as quasi-inverse. -/
theorem proEtaleClassicalSheavesModules (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ (adj :
        comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⊣
          comparisonLowerStar (ModuleCat.{u + 1} Λ) X),
      PreservesFiniteLimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ∧
      PreservesFiniteColimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ∧
      (∀ F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
        Function.Bijective (fun f : F ⟶ G ↦
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map f)) ∧
      (∀ G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
        IsClassical ((sheafCompose (Scheme.ProEt.topology X)
          (forget (ModuleCat.{u + 1} Λ))).obj G) ↔
          IsIso (adj.counit.app G)) ∧
      (∀ G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
        IsClassical ((sheafCompose (Scheme.ProEt.topology X)
          (forget (ModuleCat.{u + 1} Λ))).obj G) ↔
          ∃ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
            Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F ≅ G)) := by
  let adj := comparisonAdjunction (ModuleCat.{u + 1} Λ) X
  have hc (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
      IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget (ModuleCat.{u + 1} Λ))).obj G) ↔ IsIso (adj.counit.app G) := by
    rw [(Scheme.proEtaleClassicalSheavesImage X _).2]
    rw [← comparisonForgetIso_counit X Λ G]
    rw [isIso_comp_left_iff]
    exact (isIso_iff_of_reflects_iso _
      (sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} Λ))))
  refine ⟨adj, inferInstance, inferInstance, ?_, hc, ?_⟩
  · intro F G
    exact (Functor.FullyFaithful.ofFullyFaithful
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)).map_bijective F G
  · intro G
    exact (hc G).trans adj.isIso_counit_app_iff_mem_essImage

end AlgebraicGeometry.ProEtale
