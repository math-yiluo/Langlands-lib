/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearUniversalAction
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-! # Identity detection on the universal linear parameter scheme

Source: linear-trace invariance, proof paragraphs 1 and 2.
(blueprint: lem-amb-affine-linear-action-rigidity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- An endomorphism of the universal affine trace object is the identity if its
pullback to the identity-matrix section is the identity.
Source: blueprint proposition-purity-vector-bundles, proof paragraphs 1 and 2
(blueprint: lem-amb-affine-linear-action-rigidity).

Proof: choose the normalized data supplied by the affine-space top-trace existence
statement. Its trace is an isomorphism from this source to the constant complex;
the source does not depend on the chosen data. The constant complex is tensor-invertible,
so the source is as well. Each point of the determinant-open lies in a preconnected
set meeting the identity section, by the existing general-linear geometry lemma.
The existing identity-detection lemma for invertible complexes now applies. Its proof
identifies unit endomorphisms with ordinary sheaf maps and uses local constancy along
these preconnected sets. It does not use a cohomology class supported on a zero section.
The identity section is closed; empty schemes and dimension zero are included. -/
theorem linearAction_eq_id_of_identitySection
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (r : linearActionObject A N hA (generalLinearOpen d S).toScheme d ⟶
      linearActionObject A N hA (generalLinearOpen d S).toScheme d)
    (hr : (ordinaryFinitePullback A (glOne (c := d) (S := S))).map r = 𝟙 _) :
    r = 𝟙 _ := by
  obtain ⟨t₀, D₀, _, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  have := (htrace (generalLinearOpen d S).toScheme
    (linearUniversalInvertible N S hS d) d).2.2.1
  let e := asIso (affineTraceCounit A N hA t₀ D₀ (generalLinearOpen d S).toScheme
    (linearUniversalInvertible N S hS d) d)
  have hunit : DerivedCategory.isInvertible A (generalLinearOpen d S).toScheme
      (ordinaryFiniteUnit A (generalLinearOpen d S).toScheme) :=
    ⟨_, ⟨derivedTensorLeftUnitor _ _ _⟩, ⟨derivedTensorLeftUnitor _ _ _⟩⟩
  exact eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible glOne
    exists_isPreconnected_glOne (DerivedCategory.isInvertible.of_iso e.symm hunit) r hr

end AlgebraicGeometry.Etale
