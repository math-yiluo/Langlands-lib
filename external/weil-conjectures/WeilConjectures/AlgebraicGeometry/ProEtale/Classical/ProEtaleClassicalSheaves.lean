/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesUnit
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
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Recognizing the classical part

## References

* Stacks Project, Tag 099T
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem classicalModuleFor_iff (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    ProEtale.IsClassicalModuleFor X Λ G ↔
      ProEtale.IsClassical ((sheafCompose (Scheme.ProEt.topology X)
        (forget (ModuleCat.{u + 1} Λ))).obj G) := by
  let V := forget (ModuleCat.{u + 1} Λ)
  have h (I : Type (u + 1)) [SmallCategory I] [IsCofiltered I]
      (P : ProEtale.AffinePresentation X I) :
      IsIso (ProEtale.continuityMap P G.obj) ↔
        Function.Bijective (ProEtale.continuityMap P (G.obj ⋙ V)) := by
    rw [← CategoryTheory.isIso_iff_bijective]
    have heq :
        (preservesColimitIso V (ProEtale.sectionDiagram P G.obj)).inv ≫
          V.map (ProEtale.continuityMap P G.obj) =
            ProEtale.continuityMap P (G.obj ⋙ V) := by
      exact preservesColimitIso_inv_comp_desc V
        (ProEtale.sectionDiagram P G.obj) (ProEtale.sectionCocone P G.obj)
    rw [← heq, isIso_comp_left_iff]
    exact (isIso_iff_of_reflects_iso _ V).symm
  constructor
  · intro hG I _ _ P
    exact (h I P).mp (hG P)
  · intro hG I _ _ P
    exact (h I P).mpr (hG P)

/-- The comparison inverse image is fully faithful and its essential image is the
classical sheaves; the same comparison is an exact equivalence onto classical module
sheaves for every discrete commutative coefficient ring.
-/
theorem proEtaleClassicalSheaves (X : Scheme.{u}) :
    Nonempty
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).FullyFaithful ∧
      (∀ (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))),
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)).essImage G ↔
          ProEtale.IsClassical G) ∧
      ∀ (Λ : Type (u + 1)) [CommRing Λ],
      ∃ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
          ObjectProperty.FullSubcategory (ProEtale.IsClassicalModuleFor X Λ)),
        F ⋙ ObjectProperty.ι _ =
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X ∧
          F.IsEquivalence ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  classical
  refine ⟨(Functor.FullyFaithful.nonempty_iff_map_bijective _).2
    (Scheme.proEtaleClassicalSheavesUnit X).2, ?_, ?_⟩
  · intro G
    refine Iff.trans ?_ (Scheme.proEtaleClassicalSheavesImage X G).1
    constructor
    · rintro ⟨F, ⟨e⟩⟩
      exact ⟨F, ⟨e.symm⟩⟩
    · rintro ⟨F, ⟨e⟩⟩
      exact ⟨F, ⟨e.symm⟩⟩
  · intro Λ _
    obtain ⟨adj, hlim, hcolim, hbij, _, himage⟩ :=
      ProEtale.proEtaleClassicalSheavesModules X Λ
    let L := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X
    let P : ObjectProperty (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)) := ProEtale.IsClassicalModuleFor X Λ
    have hc (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
        P G ↔ L.essImage G := (classicalModuleFor_iff X Λ G).trans (himage G)
    have hL : Nonempty L.FullyFaithful :=
      (Functor.FullyFaithful.nonempty_iff_map_bijective L).2 hbij
    let ff := Classical.choice hL
    let : L.Full := ff.full
    let : L.Faithful := ff.faithful
    let F := P.lift L (fun A ↦ (hc _).2 (L.obj_mem_essImage A))
    let : F.EssSurj := ⟨fun G ↦ by
      obtain ⟨A, ⟨e⟩⟩ := (hc G.obj).1 G.property
      exact ⟨A, ⟨P.isoMk e⟩⟩⟩
    let : F.IsEquivalence := { }
    exact ⟨F, rfl, inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
