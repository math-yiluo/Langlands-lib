# The quotient group acting on the subring fixed by a normal subgroup

`Langlands.LocalFactor.Ramification.FixedSubringQuotient`. The Hasse–Arf theorem
(`HasseArf/Abelian.lean`) and the character sums (`HasseArf/CharacterSum.lean`) pass from a group
`G` acting on a discrete valuation ring `R` to the quotient `G ⧸ H` acting on the invariants
`R^H = FixedPoints.subring R H` of a normal subgroup. This module proves that the quotient action
satisfies the hypotheses under which those theorems are stated.

## Statement

```lean
theorem Langlands.Ramification.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_fixedSubring
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (H : Subgroup G) [H.Normal] :
    FaithfulSMul (G ⧸ H) (FixedPoints.subring R H) ∧
    PerfectField (IsLocalRing.ResidueField (FixedPoints.subring R H)) ∧
    ∃ (_ : (IsLocalRing.maximalIdeal (FixedPoints.subring R H)).LiesOver
      (IsLocalRing.maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))),
      Algebra.IsSeparable
        (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) ⧸
          IsLocalRing.maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))
        (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H))
```

In words: `G ⧸ H` acts faithfully on `R^H`; the residue field of `R^H` is perfect; the maximal
ideal of `R^H` lies over that of `(R^H)^{G/H}`; and the residue extension of `R^H` over
`(R^H)^{G/H}` is separable.

## Proof

*Faithfulness.* `G` acts faithfully on the fraction field `K` of `R` (`fracAut`,
`faithfulSMul_fractionRing`), so it is the Galois group of `K` over `K^G` (Mathlib's
`FixedPoints.toAlgAut_bijective`). Every `H`-invariant element of `K` is a quotient of
`H`-invariant elements of `R` (`exists_prod_smul`, `exists_eq_div_of_forall_smul_eq`: multiply
numerator and denominator by the other conjugates of the denominator), so an element `σ` fixing
`R^H` fixes `K^H` and lies in `H` by the Galois correspondence (`mem_of_forall_fixedPoints`). If
`σ H` and `τ H` act alike on `R^H`, then `σ⁻¹τ` fixes `R^H` and lies in `H`.

*Lies over, residue fields.* `(R^H)^{G/H}` is identified with `R^G` (`toTop`, `ofTop`), and maximal
ideals of invariants are contractions (`maximalIdeal_fixedSubring_eq_comap`), which gives the
lies-over statements. The residue fields form a tower `k(R^G) → k(R^H) → k(R)` (`phi`, `psi`,
with `psi` the identification of `k((R^H)^{G/H})` with `k(R^G)`); separability of `k(R)` over
`k(R^G)` gives that of `k(R^H)` over `k(R^G)` (`isSeparable_quotient`: the minimal polynomial over
the smaller field of the image in `k(R)` is separable and divides) and of `k(R)` over `k(R^H)`
(`isSeparable_top`). A finite separable extension below the perfect `k(R)` is perfect
(`perfectField_residueField`).

## Declarations

In the order of the file, in `Langlands.Ramification.FixedSubringQuotient`:
`map_nonZeroDivisors_eq`, `fracAut`, `fracAut_algebraMap`, `fracAut_one`, `fracAut_mul`,
`fracAutHom`, the scoped instance `mulSemiringActionFractionRing`, `smul_frac_def`,
`smul_algebraMap` (scoped `simp`), `faithfulSMul_fractionRing`, `exists_prod_smul`,
`exists_eq_div_of_forall_smul_eq`, `smul_eq_self_of_forall_fixedPoints`,
`mem_of_forall_fixedPoints`, `faithfulSMul_quotient`, `toTop`, `ofTop`, `toTop_ofTop`, `toTopHom`,
`toTopHom_surjective`, `inclHom`, `liesOver_quotient`, `liesOver_top`, `mem_maximalIdeal_sub_iff`,
`mem_maximalIdeal_subsub_iff`, `mem_maximalIdeal_top_iff`, `psi`, `psi_surjective`, `phi`,
`isSeparable_quotient`, `isSeparable_top`, `perfectField_residueField`; then
`faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_fixedSubring` in
`Langlands.Ramification`.

## Source and licence

Adapted from two files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.lean` | `dd3df56afc95f3f07e4465134fb08f71a05168b95335a92ccbea241b7b7578e1` |
| `P2M/Sol/S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.lean` | `3c45eb739409b94989d6450cb044a52baa0611b8a3321b6c1759394ebbb926ac` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files: the statement and its proof are one module; the FLT name space
`P2MW.<file>.FixedPoints.Frame` is `Langlands.Ramification.FixedSubringQuotient`, and the FLT
`export _root_.FixedPoints (…)` lines (which put Mathlib names into the proof name space) are
`open FixedPoints (…)`; `FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring`
is `Langlands.Ramification.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_fixedSubring`;
no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter I, §7, Proposition 22, printed page 22 (for `E/K`
Galois inside `L/K`, the exact sequences `1 → G(L/E) → G(L/K) → G(E/K) → 1` and their analogues for
the decomposition and inertia groups and for the residue extensions), and Chapter IV, §1, printed
page 63 (before Proposition 3): for a Galois extension `L/K` with group `G` and a normal subgroup
`H` with fixed field `K'`, the extension `K'/K` is Galois with group `G/H`; its residue extension
is a subextension of that of `L/K`.
