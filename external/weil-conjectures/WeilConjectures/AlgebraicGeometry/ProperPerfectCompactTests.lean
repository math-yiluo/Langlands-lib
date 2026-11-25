/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactRepresentatives
import WeilConjectures.AlgebraicGeometry.ProperPerfectPreservesCompact
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactDetection

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Proper perfect pushforward admits a small family of compact isomorphism tests
whose images are compact. This statement makes no reference to a right adjoint.
Source: Stacks Project, Tags 0A9R (first paragraph), 0B6G, 09M1, and 09IS.
(blueprint: lem-sc-proper-perfect-compact-tests).

Proof. Work first in the K-injective derived models with small Hom sets and the
corresponding derived models on every open. The localization equivalences transport
coproducts, their Hom comparisons, and isomorphisms to the given models, so no choice
of derived model changes the assertion. Take a set of representatives of the perfect
complexes on X, including representatives of all their shifts. Noetherian schemes
are quasi-compact and quasi-separated. Perfect compactness makes each representative
compact. Proper perfect direct image makes its image perfect on Y; compactness on Y
and eR then make its R-image compact.

To verify detection, let a morphism induce Hom bijections from all representatives.
The same holds from every perfect object and every shift. Complete the morphism to
a distinguished triangle. Exactness of shifted Hom and the bijections imply that
all Hom groups from perfect objects to its cone vanish. The objects A whose every
shift has zero Hom to this cone form a class closed under isomorphisms, shifts,
cones (by exactness), retracts, and coproducts (by their universal property).
Perfect generation makes this class the whole category. In particular the cone's
identity is zero, so the cone is zero and the original morphism is an isomorphism.
Transporting the representatives through the localization equivalence preserves
this detection property and both compactness assertions. -/
theorem properPerfect_compactTests
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
    ∃ (S : Type u) (G : S → schemeDerivedQCohCategory X),
      (∀ s, IsCompactObject (G s) ∧ IsCompactObject (R.obj (G s))) ∧
      ∀ (A B : schemeDerivedQCohCategory X) (g : A ⟶ B),
        (∀ s, Function.Bijective (fun a : G s ⟶ A ↦ a ≫ g)) → IsIso g := by
  obtain ⟨S, G, hcompact, hrep⟩ := derivedQCoh_compact_representatives X
  refine ⟨S, G, fun s ↦ ⟨hcompact s,
    properPerfect_preserves_compact f hTor R eR (G s) (hcompact s)⟩, ?_⟩
  intro A B g hg
  apply derivedQCoh_compact_detection X A B g
  intro P hP
  obtain ⟨s, ⟨e⟩⟩ := hrep P hP
  constructor
  · intro a b hab
    apply (cancel_epi e.inv).mp
    apply (hg s).injective
    simpa only [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) hab
  · intro b
    obtain ⟨a, ha⟩ := (hg s).surjective (e.inv ≫ b)
    refine ⟨e.hom ≫ a, ?_⟩
    change (e.hom ≫ a) ≫ g = b
    change a ≫ g = e.inv ≫ b at ha
    rw [Category.assoc, ha, ← Category.assoc, e.hom_inv_id, Category.id_comp]

end AlgebraicGeometry
