/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-!
# Regular divisors meeting transversely at one point

The transverse boundary calculation of the trace formula (blueprint
`lemma-cohomology-near-two-transverse-divisors`) works with two regular divisors `X, Y` of a surface
`Z` "meeting transversely at exactly one point `z`".

## Main definitions

- `AlgebraicGeometry.IsRegularDivisor i`: the morphism `i : D ⟶ Z` is an effective Cartier
  divisor (`AlgebraicGeometry.IsEffectiveCartierCenter`) with regular source.
- `AlgebraicGeometry.MeetTransverselyAt iX iY z`: the scheme-theoretic intersection
  `X ×_Z Y` is the spectrum of a field, lying over the point `z`. For two divisors on a regular
  surface this says that their local equations at `z` form a regular system of parameters of
  `𝒪_{Z,z}` and that they meet nowhere else.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A *regular divisor* of `Z`: an effective Cartier divisor `i : D ⟶ Z` whose source `D` is
a regular scheme. -/
def IsRegularDivisor {D Z : Scheme.{u}} (i : D ⟶ Z) : Prop :=
  IsEffectiveCartierCenter i ∧ IsRegular D

/-- A regular divisor is a closed immersion. -/
lemma IsRegularDivisor.isClosedImmersion {D Z : Scheme.{u}} {i : D ⟶ Z}
    (h : IsRegularDivisor i) : IsClosedImmersion i :=
  h.1.isClosedImmersion

/-- Two closed subschemes `iX : X ⟶ Z` and `iY : Y ⟶ Z` *meet transversely at exactly the
point `z`*: their scheme-theoretic intersection `X ×_Z Y` is the spectrum of a field, mapping to
`z`. -/
def MeetTransverselyAt {X Y Z : Scheme.{u}} (iX : X ⟶ Z) (iY : Y ⟶ Z) (z : Z) : Prop :=
  ∃ (K : Type u) (_ : Field K) (pX : Spec (.of K) ⟶ X) (pY : Spec (.of K) ⟶ Y),
    IsPullback pX pY iX iY ∧ Set.range (pX ≫ iX) = {z}

/-- Two closed subschemes meeting transversely at `z` meet set-theoretically exactly at `z`. -/
lemma MeetTransverselyAt.range_inter_range {X Y Z : Scheme.{u}} {iX : X ⟶ Z} {iY : Y ⟶ Z}
    {z : Z} (h : MeetTransverselyAt iX iY z) :
    Set.range iX ∩ Set.range iY = {z} := by
  obtain ⟨K, _, pX, pY, hp, hz⟩ := h
  rw [← hz]
  ext w
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨hp.isoPullback.inv.base t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, hp.isoPullback_inv_fst, Scheme.Hom.comp_apply,
      ht₁]
  · rintro ⟨t, rfl⟩
    refine ⟨⟨pX.base t, rfl⟩, ⟨pY.base t, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, hp.w]

end AlgebraicGeometry
