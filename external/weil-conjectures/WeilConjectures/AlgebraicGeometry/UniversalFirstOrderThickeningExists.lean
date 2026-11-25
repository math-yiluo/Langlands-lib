/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningAffineCase
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOpenPieces
import WeilConjectures.RingTheory.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningExistence

/-!
# Existence and uniqueness of universal first order thickenings

Source: Stacks Project, More on Morphisms, Lemma 37.7.1 (Tag 04F3), and the opening
paragraph of Section 37.7 (Tag 04F2)
(blueprint: lem-weil-pbc-universal-first-order-thickening-exists).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A formally unramified morphism admits a universal first order thickening, and any two
such thickenings admit exactly one compatible morphism, which is an isomorphism.
Source: Stacks Project, Tags 04F3 and 04F2
(blueprint: lem-weil-pbc-universal-first-order-thickening-exists).

Proof plan, following the seven steps of the node:
1. Uniqueness follows from `IsUniversalFirstOrderThickening.unique`: apply the two universal
   properties to the identity of `Z`, and use uniqueness to identify the inverse composites.
2. Cover `Z` by affine opens mapping into affine opens of `X` (def-pc-scheme). Restriction
   preserves formal unramifiedness (lem-weil-pbc-formally-unramified-open-restriction).
   Identify the pieces with spectra (def-weil-affine-spectrum) and apply
   lem-weil-pbc-affine-formally-unramified-iff-ring and
   lem-weil-pbc-ring-universal-first-order-thickening. The affine-case lemma
   lem-weil-pbc-universal-thickening-affine-case gives universal scheme thickenings, and
   lem-weil-pbc-universal-thickening-open-pieces lets their base maps land in `X`.
3. A first order thickening is a homeomorphism on points (def-sbc-first-order-thickening).
   Thus each overlap determines an open in each thickened piece. By the open-pieces lemma
   these are universal for the overlap, so uniqueness gives their transition isomorphisms.
4. On triple overlaps both transition composites extend the same map over `X`; uniqueness
   makes them equal. Factoring through the corresponding opens uses def-weil-open-immersion.
5. Glue the pieces using lem-weil-pbc-glue-schemes. Glue the maps to `X` and the maps from
   `Z` using lem-weil-pbc-scheme-morphism-gluing. Their composites agree with `h` on the
   cover, giving a morphism over `X` (def-weil-scheme-over-base).
6. The inverse image of each glued piece is its original open of `Z`. The affine-cover
   criterion lem-weil-pbc-closed-immersion-affine-cover-criterion proves the global map
   is a closed immersion (def-weil-closed-immersion). Its kernel ideal sheaf
   (def-sbc-closed-immersion-ideal-sheaf) has square zero locally, hence globally. This
   gives a first order thickening; the pieces and their intersections remain universal.
7. For a test thickening `T ⊆ T'`, pull the covering of `Z` back to `T` and transfer it to
   `T'`. The open-pieces lemma provides test thickenings on this cover. Local universal
   properties give lifts. On intersections factor through the corresponding overlaps
   using def-weil-open-immersion and use uniqueness to make the lifts agree. The morphism
   gluing lemma gives a global lift; the same local uniqueness proves its uniqueness. -/
theorem FormallyUnramified.exists_universalFirstOrderThickening {Z X : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] :
    (∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h') ∧
    ∀ (Z₁ Z₂ : Scheme.{u}) (i₁ : Z ⟶ Z₁) (h₁ : Z₁ ⟶ X)
      (i₂ : Z ⟶ Z₂) (h₂ : Z₂ ⟶ X),
      IsUniversalFirstOrderThickening h i₁ h₁ →
      IsUniversalFirstOrderThickening h i₂ h₂ →
        (∃! φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ ∧ i₁ ≫ φ = i₂) ∧
          ∀ φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ → i₁ ≫ φ = i₂ → IsIso φ := by
  constructor
  · exact FormallyUnramified.exists_universalFirstOrderThickening_existence h
  · intro Z₁ Z₂ i₁ h₁ i₂ h₂ H₁ H₂
    exact IsUniversalFirstOrderThickening.unique h i₁ h₁ i₂ h₂ H₁ H₂

end AlgebraicGeometry
