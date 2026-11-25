# The valuation of the fixed subring and the order of the inertia group

`Langlands.LocalFactor.Ramification.FixedSubringValuation`. Two facts on a discrete valuation ring
over the invariants of a finite group: the order of the zeroth lower group (the inertia group) is
the ramification index, and the valuation of the ring restricted to the invariants is that
order times the valuation of the invariants. The second is the scaling factor `e = |H_0|` in the
monogenic form of Herbrand's theorem (`Herbrand/LowerQuotient.lean`).

## Statements

Name space `Langlands.Ramification`.

```lean
theorem card_lowerGroup_zero_eq_ramificationIdxIn {A : Type*} [CommRing A] [IsLocalRing A]
    {B : Type*} [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    {G : Type*} [Group G] [MulSemiringAction G B]
    [IsDedekindDomain A] [Module.Finite A B] [IsGaloisGroup G A B] [Finite G]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A)]
    [Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)]
    (hp : IsLocalRing.maximalIdeal A ≠ ⊥) :
    Nat.card (lowerGroup B G 0) = (IsLocalRing.maximalIdeal A).ramificationIdxIn B

theorem addVal_coe_eq_lowerGroupCard_zero_mul_addVal_fixedPoints
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] [FaithfulSMul H R]
    [IsDiscreteValuationRing (FixedPoints.subring R H)]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R H))]
    [Algebra.IsSeparable
      (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (z : FixedPoints.subring R H) :
    IsDiscreteValuationRing.addVal R (z : R) =
      (lowerGroupCard R H 0 : ℕ∞) * IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z
```

## Proofs

The first: `lowerGroup B G 0` is the inertia group of `m_B` (`lowerGroup_zero`), and Mathlib's
`Ideal.card_inertia_eq_ramificationIdxIn` gives its order once its separability hypothesis is
supplied by `hasSeparableResidueFieldsAt_maximalIdeal_of_isSeparable` (`SeparableResidueField.lean`);
flatness is Mathlib's instance for a torsion-free module over a Dedekind domain.

The second: `R` is finite over its invariants (`FixedSubringValuation.module_finite_fixedSubring`:
`H` is a Galois group of the fraction fields, and `R` is the integral closure of the invariants in
the larger one), and `H` is a Galois group of `R` over the invariants (`isGaloisGroup_fixedSubring`).
For a uniformizer `π` of the invariants, `v_R(π)` is the ramification index
(`addVal_algebraMap_irreducible_eq_ramificationIdx`), which by the first theorem is `|H_0|`; writing
`z = u π^n` with `u` a unit gives `v_R(z) = |H_0| n` (`addVal_map_eq_mul_of_irreducible`).

## Declarations

In the order of the file: `card_lowerGroup_zero_eq_ramificationIdxIn`; in
`Langlands.Ramification.FixedSubringValuation`: `module_finite_fixedSubring`,
`addVal_algebraMap_irreducible_eq_ramificationIdx`, `addVal_map_eq_mul_of_irreducible`; then
`addVal_coe_eq_lowerGroupCard_zero_mul_addVal_fixedPoints`.

## Source and licence

Adapted from four files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean` | `920e933d99ed4a3f77fc0ffe23fc4d779017e5a2f0fc3fc21a7605b4fb95e12a` |
| `P2M/Sol/S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean` | `5f0888fa3a0329beb5585321af14403a756b681d89b0e6b9a7b54c99cb09d4d2` |
| `Theorems/Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean` | `03c54dc7ab834efe2bea7919c0e1346eabdc1e05acf8d49f6ac8ba038f35945a` |
| `P2M/Sol/S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean` | `e55a7e5135f6892f57df8ff28650f9a77192d3360861b721bc887403fd9d27ff` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` lists none
of these four files; it lists `Definitions/Def_Compat_Mathlib430.lean` (Mathlib text), whose lemma
the first FLT proof used and which is not used here. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files:

- The four files are one module; statements are on `lowerGroup` and `lowerGroupCard`; upstream's
  `card_lowerRamificationGroup_zero_eq_ramificationIdxIn` and
  `IsDiscreteValuationRing.addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints` are
  `Langlands.Ramification.card_lowerGroup_zero_eq_ramificationIdxIn` and
  `…addVal_coe_eq_lowerGroupCard_zero_mul_addVal_fixedPoints`; the proof name space
  `P2MW.<file>.HerbrandPortG3` is `Langlands.Ramification.FixedSubringValuation`.
- The proof of the first theorem: the FLT proof applied `Ideal.card_inertia_eq_ramificationIdxIn'`,
  a lemma that `Def_Compat_Mathlib430` adapted from Mathlib v4.30.0 (Dedekind domains, torsion-free,
  separability of the quotient fields). It now applies the present Mathlib's
  `Ideal.card_inertia_eq_ramificationIdxIn` and the lemma of `SeparableResidueField.lean`.
- The FLT statement file erased the instances `isLocalRing_fixedSubring` and
  `isLocalHom_fixedSubring_subtype` while elaborating its statement; here the statement is
  elaborated with them, so the `IsLocalRing` instance of the invariants inside the statement is a
  different (definitionally equal) proof. The deprecated `Ideal.ramificationIdx_spec` is replaced by
  `Ideal.ramificationIdx'_spec`; no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter I, §7, Proposition 21 b) and its Corollary, printed
page 22 (ramification index and valuations in an extension: `w` prolongs `w_T` with index `e`, and
`[L : K_T] = e` when the residue extension is separable, so that the inertia group has order `e`),
and Chapter IV, §1, Proposition 1, printed page 62 (`G_0` is the inertia group).
