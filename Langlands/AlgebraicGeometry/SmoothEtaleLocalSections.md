# Etale local sections of smooth surjective scheme morphisms

Author: Worker 766.

This module is `Langlands.AlgebraicGeometry.SmoothEtaleLocalSections`. It
imports only the algebraic core `Langlands.CommutativeAlgebra.EtaleLocalSections`
(and through it Mathlib).

## Purpose and provenance

The main theorem `hasEtaleLocalSections_of_smooth` is the content of The Stacks
Project, More on Morphisms, Lemma 37.38.6 (Tag 055U), registered as
`stacks-055U-smooth-etale-local-sections-2026-11-02`, which cites EGA IV,
Corollaire 17.16.3 (ii). The source gives, through every point in the image of
a smooth morphism, an etale neighborhood mapping to the source over the
target. Here, for a surjective smooth morphism, one such neighborhood is
chosen through each point of the target, and their disjoint union is taken.
This packaging into a single surjective etale cover is derived, and is the
form used by the statement `SmoothSurjectiveEtaleLocalSectionsStatement`
(task `9fbac921`, statement candidate `5fd39fe6` by Worker 59). Its proof is
then `fun _ _ f _ _ => hasEtaleLocalSections_of_smooth f`. This module does
not import that statement, so it does not depend on its publication.

The proof follows neither of the two proofs in the source. It reduces to
standard etale algebras over polynomial rings, which are treated in the
Markdown of `Langlands.CommutativeAlgebra.EtaleLocalSections`.

## Declarations

- `HasEtaleLocalSections f`, for a morphism `f : W ⟶ T` in `Scheme.{u}`, is
  the proposition that there are `V : Scheme.{u}`, an etale surjective
  `e : V ⟶ T` and `s : V ⟶ W` with `s ≫ f = e`. Equivalently, the pullback of
  `f` along some surjective etale morphism has a section. It is a
  per-morphism form of the conclusion of the statement
  `SmoothSurjectiveEtaleLocalSectionsStatement` (Stacks 055U, packaged as one
  cover). No quasi-compactness of `e` is required.
- `exists_etale_algHom_of_smooth`: let `S` be a smooth `R`-algebra and `p` a
  prime of `S`. There are an etale `R`-algebra `R'`, an `R`-algebra map
  `S → R'`, and a prime of `R'` whose preimage in `R` equals the preimage of
  `p`. Mathlib's `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` gives
  `g ∉ p` such that `S[1/g]` is standard etale over a polynomial ring
  `R[X₁, …, Xₙ]`. The prime `p` extends to a prime of `S[1/g]` with preimage
  `p`. Apply `exists_etale_algHom_of_isStandardEtale` to `S[1/g]` and this
  prime, then precompose with `S → S[1/g]`.
- `exists_etale_spec_of_smooth`: let `f : W ⟶ T` be smooth and `x` a point of
  `W`. There are a ring `R'`, an etale morphism `e : Spec R' ⟶ T` whose range
  contains `f x`, and `s : Spec R' ⟶ W` with `s ≫ f = e`. Mathlib's
  `Smooth.exists_isStandardSmooth` is used only to obtain affine opens `U` of
  `T` and `V` of `W` with `x ∈ V` and `V ≤ f⁻¹ U`. The ring map
  `f.appLE U V : Γ(T, U) → Γ(W, V)` is smooth by `Scheme.Hom.smooth_appLE`.
  Apply the previous theorem to `Γ(T, U) → Γ(W, V)` at
  the prime of `x`, which gives `R'` and `ψ : Γ(W, V) → R'`. Put
  `e = Spec R' ⟶ Spec Γ(T, U) ⟶ T` and `s = Spec R' ⟶ Spec Γ(W, V) ⟶ W`,
  using the open immersions `fromSpec` of the affine opens.
  - `e` is etale as the composite of `Spec` of an etale ring map and an open
    immersion.
  - The prime of `R'` from the previous theorem maps to the image of the prime
    of `x` in `Spec Γ(T, U)`. That point maps to `f x` by Mathlib's
    `IsAffineOpen.SpecMap_appLE_fromSpec` and `fromSpec_primeIdealOf`.
  - `s ≫ f = e` follows from the same lemma, together with the fact that `ψ`
    is a `Γ(T, U)`-algebra map.
- `hasEtaleLocalSections_of_smooth`: if `f : W ⟶ T` is smooth and
  surjective, then `HasEtaleLocalSections f`. Choose
  for each point `t` of `T` a preimage under `f`. The previous theorem then
  gives `Spec R'_t`, `e_t` and `s_t`. Let `V` be the coproduct
  `∐ t, Spec R'_t` in `Scheme.{u}`. The index type is the point type of `T`,
  which lies in `Type u`, so `V : Scheme.{u}`. Let
  `e = Sigma.desc e_t` and `s = Sigma.desc s_t`.
  - `e` is etale because being etale is local on the source
    (`IsZariskiLocalAtSource.sigmaDesc`, with the instance supplied by
    `HasRingHomProperty.instIsZariskiLocalAtSource` for `@Etale`).
  - `e` is surjective because the ranges of the `e_t` cover `T`
    (`Surjective.sigmaDesc_of_union_range_eq_univ`).
  - `s ≫ f = e` is checked on each summand.

`hasEtaleLocalSections_of_smooth` uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
