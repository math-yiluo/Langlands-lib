# Separable residue field extensions over a local Dedekind domain

`Langlands.LocalFactor.Ramification.SeparableResidueField`. One lemma that connects two ways of
saying that a residue field extension is separable. Mathlib's statement of the order of an
inertia group, `Ideal.card_inertia_eq_ramificationIdxIn`, assumes
`Algebra.HasSeparableResidueFieldsAt R S p`: for every prime `q` of `S` over `p`, the extension of
residue fields `κ(p) → κ(q)` is separable. The ramification theory of this directory assumes
instead that `R ⧸ m_R → S ⧸ m_S` is separable. For a local Dedekind domain over a local domain
these agree, because the maximal ideal is the only prime over `m_R`.

## Statement

```lean
theorem Langlands.Ramification.hasSeparableResidueFieldsAt_maximalIdeal_of_isSeparable
    {A B : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A)]
    [Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)]
    (hp : IsLocalRing.maximalIdeal A ≠ ⊥) :
    Algebra.HasSeparableResidueFieldsAt A B (IsLocalRing.maximalIdeal A)
```

## Proof

Let `q` be a prime of `B` over `m_A`. It is not zero: the algebra map is injective
(`FaithfulSMul.algebraMap_injective`, from torsion-freeness), so `q = 0` would give `m_A = 0`. A
non-zero prime of a Dedekind domain is maximal, and the maximal ideal of a local ring is `m_B`.
At a maximal ideal the residue field `κ(q)` is the quotient `B ⧸ q`, and Mathlib's
`Algebra.isSeparable_residueField_iff` turns the separability of the quotients into that of the
residue fields.

## Declarations

`hasSeparableResidueFieldsAt_maximalIdeal_of_isSeparable`.

## Source and licence

This file is the Library's. It replaces, together with Mathlib's
`Ideal.card_inertia_eq_ramificationIdxIn`, the lemma `Ideal.card_inertia_eq_ramificationIdxIn'`
that the Anthropic FLT development (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`) adapted
from Mathlib v4.30.0 in `Definitions/Def_Compat_Mathlib430.lean`; the FLT text is not used. Its
only user is `card_lowerGroup_zero_eq_ramificationIdxIn` (`FixedSubringValuation.lean`).

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter I, §§4–7 (extensions of Dedekind domains, residue
extensions and ramification indices): the prime ideals of `B` over `p`, the ramification index and
the residue degree, printed pages 13–14 (with Proposition 10, printed page 14), and §7,
Proposition 21 and its Corollary, printed page 22 (with separable residue extension the inertia
group has order `e`).
