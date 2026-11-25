/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedSectionPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsComparisonSections
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsComparisonSheafification

/-! # Derived sections for acyclic quasi-coherent pushforward

Source: Stacks Project, Perfect Complexes, Tags 08D4, 08D5 and 0AVW, and
Cohomology, Tag 0D5X (blueprint: lem-sc-qcoh-acyclic-derived-sections-comparison).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Derived sections over the inverse images of affine opens compute sections of
cohomology, naturally in the derived object and compatibly with restriction. The
full section cohomology presheaf sheafifies to the cohomology of derived direct image.

Source: Stacks Project, Tags 08D4, 08D5, 0AVW and 0D5X
(blueprint: lem-sc-qcoh-acyclic-derived-sections-comparison).

Proof: (1) For an affine open V, restrict the injective resolution and derived direct
image to f⁻¹V and V, using lem-sc-ringed-space-restrict-injective-resolution and
lem-pc-restrict-derived-direct-image-open. Higher direct images are quasi-coherent
(lem-pc-finite-support-hi); affine vanishing (pqf-lem-affine-vanishing) and Leray
(lem-pc-leray-degenerate-sections) imply that sections on f⁻¹V are acyclic on every
quasi-coherent module. Sections preserve countable products.
(2) Shift to degree zero. Apply lem-pc-unbounded-derived-functor-cohomological-bound
with N = 1 to the negative truncation: its derived sections vanish in degrees ≥ 0.
The truncation triangle therefore removes the unbounded negative tail.
(3) Apply lemma-uniform-bound-proper-direct-image--1 to the bounded-below positive truncation. Its
positive columns vanish by (1), leaving only sections of the cohomology sheaf. All maps are
functorial, both in the derived object and in affine-open restriction; they produce
the first natural isomorphism of module presheaves on the full affine-open category.
(4) Compute using a K-injective representative I. The presheaf is the sectionwise
cohomology of f_*I. Cohomology in module sheaves is the sheafification of this
presheaf cohomology (Tag 0D5X), yielding the second natural isomorphism. -/
theorem qcoh_acyclic_derived_sections_comparison {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (i : ℤ) :
    Nonempty
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i ⋙
          PresheafOfModules.pushforward₀
            (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
            (moduleRings Y.toRingedSpace).obj ≅
        (schemeDerivedQCohProperty X).ι ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i ⋙
          RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          SheafOfModules.forget (moduleRings Y.toRingedSpace) ⋙
          PresheafOfModules.pushforward₀
            (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
            (moduleRings Y.toRingedSpace).obj) ∧
    Nonempty
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings Y.toRingedSpace).obj) ≅
        (schemeDerivedQCohProperty X).ι ⋙ schemeHigherDirectImage f i) := by
  obtain ⟨sectionsIso⟩ :=
    qcoh_acyclic_derived_sections_comparison_sections f hacyc i
  obtain ⟨sheafificationIso⟩ :=
    qcoh_acyclic_derived_sections_comparison_sheafification f hacyc i
  exact ⟨⟨sectionsIso⟩, ⟨sheafificationIso⟩⟩

end AlgebraicGeometry
