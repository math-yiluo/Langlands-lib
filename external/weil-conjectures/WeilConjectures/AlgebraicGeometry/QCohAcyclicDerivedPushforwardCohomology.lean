/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheafificationAffineRestriction

/-! # Cohomology of acyclic quasi-coherent derived pushforward

Source: Stacks Project, Tags 08D4 and 08D5, and the cohomology display in the proof
of Tag 0AVW (blueprint: lem-sc-qcoh-acyclic-derived-pushforward-cohomology).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If higher direct images vanish on quasi-coherent modules, cohomology of unbounded
 derived pushforward is naturally isomorphic to direct image of cohomology.
Source: Stacks Project, Tags 08D4, 08D5 and 0AVW
(blueprint: lem-sc-qcoh-acyclic-derived-pushforward-cohomology).

Proof: (1) On every affine open V of Y, qcqs direct image preserves quasi-coherence
(Tags 01XJ and 01XB). Leray and affine vanishing show that sections on f⁻¹V have no
positive derived functors on quasi-coherent modules. Sections commute with countable
products. Apply lem-sc-qcoh-acyclic-derived-sections-comparison, using Tag 08D4 with
N = 1, to identify H^i(RΓ(f⁻¹V,E)) with Γ(f⁻¹V,H^i(E)), naturally in E and in V.
(2) This identifies the derived-section cohomology presheaf on the affine basis with
V ↦ Γ(V,f_*H^i(E)). By the final clause of the same section-comparison node, its
sheafification is H^i(Rf_*E), whereas the latter presheaf is the restriction of the
sheaf f_*H^i(E).
(3) The universal property of sheafification (def-weil-pbc-sheafification) glues these
restriction-compatible identifications to the displayed sheaf isomorphism. The section
comparison and derived direct image are functorial in E, so the isomorphism is natural. -/
theorem qcoh_acyclic_derived_pushforward_cohomology {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (i : ℤ) :
    Nonempty ((schemeDerivedQCohProperty X).ι ⋙ schemeHigherDirectImage f i ≅
      (schemeDerivedQCohProperty X).ι ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i ⋙
        RingedSpace.moduleDirectImage f.toLRSHom.toShHom) := by
  obtain ⟨⟨sectionsIso⟩, ⟨pushforwardIso⟩⟩ :=
    qcoh_acyclic_derived_sections_comparison f hacyc i
  obtain ⟨sheafIso⟩ := module_sheafification_iso_of_affine_restriction Y
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i)
    ((schemeDerivedQCohProperty X).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom) sectionsIso
  exact ⟨pushforwardIso.symm ≪≫ sheafIso⟩

end AlgebraicGeometry
