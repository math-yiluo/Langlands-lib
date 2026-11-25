/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
import WeilConjectures.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore

/-! # Derived sheafification on the localized affine site

Source: Stacks Project, Tag 06Z0.
(blueprint: lem-pc-affine-localized-derived-sheafification).
-/

@[expose] public section

universe u wR w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Affine sheafification factors through a full functor from the module derived category.
Source: Stacks Project, Tag 06Z0, Lemma perfect-lemma-affine-compare.
(blueprint: lem-pc-affine-localized-derived-sheafification).

Proof: Apply the affine quasi-coherent derived equivalence to the spectrum of Gamma(X,U).
Compose its functor with the fully faithful inclusion of the quasi-coherent derived
subcategory. Restriction along the affine spectrum isomorphism and the equivalence of
sheaves on U with sheaves on the localized site are exact equivalences of abelian
categories. They induce equivalences of derived categories. Compose these with the
preceding functor to obtain G, which is fully faithful and in particular full. Whisker
the tilde factorization isomorphism with these transport equivalences, and compose with
their localization factorization isomorphisms. This gives the stated natural isomorphism
between Q followed by G and the explicitly constructed termwise affine sheafification
followed by Q. No choice of a complex representative is involved. The same construction
works on the empty affine spectrum; all its module and sheaf categories are zero. -/
theorem affine_localized_derived_sheafification (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U)
    [HasDerivedCategory.{wR} (ModuleCat.{u} (X.presheaf.obj (.op U)))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ G : DerivedCategory (ModuleCat.{u} (X.presheaf.obj (.op U))) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)),
      G.Full ∧ Nonempty (DerivedCategory.Q ⋙ G ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q)  := by
  let R := X.presheaf.obj (.op U)
  let : HasDerivedCategory (SheafOfModules.{u}
    (moduleRings (Spec R).toRingedSpace)) := HasDerivedCategory.standard _
  obtain ⟨e, ⟨c⟩, _, _⟩ := exists_affineQCohDerivedEquivalence_core R
  obtain ⟨E, ⟨t⟩⟩ := affine_localized_site_derived_transport X U hU
  let G := (e.functor ⋙ (schemeDerivedQCohProperty (Spec R)).ι) ⋙ E.functor
  refine ⟨G, inferInstance, ⟨?_⟩⟩
  exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight c E.functor ≪≫ t


end AlgebraicGeometry.Scheme
