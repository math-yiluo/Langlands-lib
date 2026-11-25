/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.AlgebraicGeometry.ProperPerfectDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactRepresentatives
import WeilConjectures.AlgebraicGeometry.ProperPerfectTransportCompact

/-! # Compactness preserved by proper perfect pushforward

Source: Stacks Project, Tags 09M1 and 0B6G; first paragraph of Tag 0A9R.
(blueprint: lem-sc-proper-perfect-preserves-compact).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Proper perfect pushforward preserves compact quasi-coherent derived objects.
Source: Stacks Project, Tags 09M1, 0B6G, and the first paragraph of Tag 0A9R.
(blueprint: lem-sc-proper-perfect-preserves-compact).

Proof: Noetherian schemes are quasi-compact and quasi-separated. Use K-injective
resolutions and the uniqueness of localization to work in small-Hom derived
models on X, Y, and all their opens. These equivalences commute with homology,
derived restriction, and derived direct image, and preserve coproducts and the
additive Hom comparisons defining compactness. Tag 09M1 identifies the given
compact object P with a perfect object in the small model: affine restriction
preserves compactness by its direct-sum-preserving right adjoint, and the affine
compact-object criterion gives local bounded finite-projective representatives.
The stalkwise finite Tor assumption is the perfect-morphism criterion, so apply
proper_perfect_directImage_perfect (Tag 0B6G) to that perfect object.
Its image is perfect on Y and therefore compact by perfectObjectCompact.
Transport back to the original models. The component eR.app P identifies the
ambient image with (R.obj P).obj. Since the inclusion of D_QCoh is fully faithful,
this isomorphism lifts to D_QCoh(Y); isomorphic objects have identical compactness
comparisons under the induced additive Hom equivalences. Thus R.obj P is compact.
No right adjoint of R, generator, or representative family is assumed. -/
theorem properPerfect_preserves_compact
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsProper f]
    (hTor : ∀ x : X, ∃ n : ℕ,
      ∀ (N : ModuleCat.{u} (Y.presheaf.stalk (f x))) (i : ℕ), n < i →
        IsZero (((Tor (ModuleCat.{u} (Y.presheaf.stalk (f x))) i).obj
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))).obj N))
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (eR : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
    ∀ P : schemeDerivedQCohCategory X, IsCompactObject P → IsCompactObject (R.obj P) := by
  dsimp
  set_option linter.style.haveILetI false in
    letI : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  intro P hP
  obtain ⟨hX⟩ := noetherian_open_derived_categories_exists X
  obtain ⟨hY⟩ := noetherian_open_derived_categories_exists Y
  set_option linter.style.haveILetI false in
    letI := hX
  set_option linter.style.haveILetI false in
    letI := hY
  exact properPerfect_transport_compact f hTor R eR P
    (compact_isPerfect_of_isNoetherian X P hP)

end AlgebraicGeometry
