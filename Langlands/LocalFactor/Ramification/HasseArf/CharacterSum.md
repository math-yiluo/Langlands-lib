# Integrality of the lower-group sum of a character

`Langlands.LocalFactor.Ramification.HasseArf.CharacterSum`. For a finite group acting on a discrete
valuation ring and a character of the group, the weighted count of the lower groups on which the
character is not trivial,

`∑_{i ≥ 0} |G_{i+1}|/|G_0| · [χ is not trivial on G_{i+1}]`,

is a natural number. For the Galois group of a finite extension of local fields this is the
exponent of the Swan conductor of a one-dimensional character, and the Library's
`Herbrand/CharacterExponentIntegrality.lean` derives from it that the Artin and Swan conductors of
one-dimensional representations are natural numbers.

## Statements

Name space `Langlands.Ramification`; both theorems are stated with classical decidability of the
condition in the `if`.

```lean
theorem finsum_lowerGroup_indicator_comp_mk_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] {A : Type*} [CommGroup A] (χ : G ⧸ H →* A) :
    ∑ᶠ i : ℕ,
        (Nat.card (lowerGroup R G (i + 1)) : ℚ) / (Nat.card (lowerGroup R G 0) : ℚ) *
          (if ∀ σ ∈ lowerGroup R G (i + 1), χ (QuotientGroup.mk σ) = 1 then 0 else 1) =
      ∑ᶠ j : ℕ,
        (Nat.card (lowerGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) : ℚ) /
            (Nat.card (lowerGroup (FixedPoints.subring R H) (G ⧸ H) 0) : ℚ) *
          (if ∀ τ ∈ lowerGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1), χ τ = 1 then 0 else 1)

theorem exists_finsum_lowerGroup_indicator_eq_natCast
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (ψ : G →* ℂˣ) :
    ∃ m : ℕ,
      ∑ᶠ i : ℕ,
        (Nat.card (lowerGroup R G (i + 1)) : ℚ) / (Nat.card (lowerGroup R G 0) : ℚ) *
          (if ∀ σ ∈ lowerGroup R G (i + 1), ψ σ = 1 then 0 else 1) = m
```

The first says that the sum is unchanged when a character of `G ⧸ H` is computed with the lower
groups of `G ⧸ H` acting on the invariants `R^H`; the second needs neither commutativity nor a
Galois hypothesis.

## Proofs

Let `d` be the first index with `χ` trivial on `G_d` (`firstTriv`; it exists because the lower groups
end in `⊥`, `exists_index_eq_bot_of_antitone_of_iInf_eq_bot`). Only the terms `i + 1 < d` are non-zero,
so the sum is `(|G_1| + ⋯ + |G_{d-1}|)/|G_0| = φ(d - 1)` (`finsum_indicator_eq_herbrandPhiRat`).
Moreover, for `v > 0`, `χ` is not trivial on the upper group `G^v` exactly when `v ≤ φ(d - 1)`
(`not_triv_upper_iff`).

*Quotients.* `χ ∘ mk` is not trivial on `G^v` exactly when `χ` is not trivial on its image
`(G/H)^v` (`upperGroupRatQuotientCompat_of_isSeparable_residueField`); so the two values of `φ` are
characterised by the same condition on positive rationals and are equal
(`eq_of_forall_pos_le_iff`).

*Integrality.* Apply the quotient statement with `H = ker ψ`: `G ⧸ ker ψ` embeds into `ℂˣ`, so it is
cyclic, and it acts on `R^{ker ψ}` with all the hypotheses
(`faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_fixedSubring`). The induced character
is injective, so `d - 1` is a break of the lower filtration of the quotient, and the cyclic
Hasse–Arf theorem (`hasseArfChain_lowerGroup_of_isCyclic`) makes `φ(d - 1)` an integer.

## Declarations

In the order of the file, in `Langlands.Ramification.HasseArf.CharacterSum`: `Triv`, `Triv.mono`,
`firstTriv`, `triv_iff_firstTriv_le`, `finsum_indicator_eq_herbrandPhiRat`, `upperGroupRatIndex_pos`,
`not_triv_upper_iff`, `exists_index_eq_bot_of_antitone_of_iInf_eq_bot`, `eq_of_forall_pos_le_iff`;
`finsum_lowerGroup_indicator_comp_mk_eq` in `Langlands.Ramification`;
`HasseArf.CharacterSum.exists_index_lowerGroup_eq_bot`; then
`exists_finsum_lowerGroup_indicator_eq_natCast`.

## Source and licence

Adapted from four files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Theorems/Thm_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.lean` | `6f17b4d43ef5174abf68c3e64a4241de070ee9b1096386fd9b8a22362f4bbf17` |
| `P2M/Sol/S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.lean` | `748f75794a7b44a5608266a3c11a014e255ccf4caae3e4d30c80c96d80b6cfa9` |
| `Theorems/Thm_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.lean` | `8ab112d43a337b90aaedeb5f5f71d26f0dd2be1f2c7a4234734aef24c09eb186` |
| `P2M/Sol/S_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.lean` | `bc2e1b27c67f69643d3c9bfcfafa8ba27f2722e14fbc6d869d6a16e8df6805e8` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files:

- The four files are one module. Both FLT proofs carried the name space
  `P2MW.<file>.IsLocalRing.SwanInfl`; it is `Langlands.Ramification.HasseArf.CharacterSum`, and the
  lemmas both copies had are kept once.
- Two helpers are renamed so that they cannot be confused, inside their name space, with the
  Library's `exists_lowerGroup_eq_bot` and `exists_eq_bot_of_antitone_of_iInf_eq_bot` (which have
  different statements): `SwanInfl.exists_lowerRamificationGroup_eq_bot` is
  `exists_index_lowerGroup_eq_bot` and `SwanInfl.exists_eq_bot_of_antitone_of_iInf_eq_bot` is
  `exists_index_eq_bot_of_antitone_of_iInf_eq_bot`; the FLT file's `open IsLocalRing hiding …`, which
  avoided the first confusion, is `open IsLocalRing`.
- Statements are on `lowerGroup`; upstream's `IsDiscreteValuationRing.finsum_lowerRamificationGroup_indicator_comp_mk_eq`
  and `…exists_finsum_lowerRamificationGroup_indicator_eq_natCast` are
  `Langlands.Ramification.finsum_lowerGroup_indicator_comp_mk_eq` and
  `…exists_finsum_lowerGroup_indicator_eq_natCast` (definitionally equal statements). The FLT
  erasure of two `simp` lemmas is kept for each proof, in its section. The deprecated `if_pos`,
  `if_neg` are replaced by `ite_eq_left`, `ite_eq_right`; no options are set.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter VI, §2, Proposition 5 and its Corollary, printed
page 102 (for a character `χ` of degree one, the Artin conductor is `f(χ) = φ(c_χ) + 1`, `c_χ` the
last lower index where `χ` is non-trivial; for `χ` non-trivial on `G_0` the sum here is
`f(χ) - 1 = φ(c_χ)`), and Chapter V, §7, Theorem 1 (Hasse–Arf), printed page 93, which makes it an
integer. Serre's §2 has only the Artin character; the Swan character is that of P. Deligne, *Les
constantes des équations fonctionnelles des fonctions L* (1973), §4.5, (4.5.1), printed page 537.
