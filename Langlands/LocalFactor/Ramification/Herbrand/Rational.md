# The Herbrand functions on the rationals and upper groups with rational index

`Langlands.LocalFactor.Ramification.Herbrand.Rational`. For a group `G` acting on a local ring
`R`, with `g_i = |G_i|` the order of `lowerGroup R G i`, this module defines Herbrand's function
`φ` on `ℚ`, its inverse `ψ`, and the upper groups `G^v` for rational `v`. These are auxiliary
functions: the Library's Herbrand functions are the real ones `Padic.herbrandPhi`,
`Padic.herbrandPsi` and `Padic.upperRamificationGroup` of finite p-adic extensions
(`Herbrand/Finite.lean`, `Herbrand/Real.lean`). The quotient and Hasse–Arf theorems of this
directory are proved for the rational functions, and the bridges `Herbrand/LocalQuotientProof.lean`
(`QuotientBridge`) and `Herbrand/QuotientProof.lean` (`HerbrandBridge`) prove that the two agree at
rational arguments (`herbrandPhi_ratCast`, `ceil_herbrandPsi_ratCast`,
`upperRamificationGroup_ratCast`).

## Statements

Name space `Langlands.Ramification`; `R` a local commutative ring, `G` a group with
`[MulSemiringAction G R]`; most results assume `[Finite G]`.

- Orders of the lower groups and the function `φ`:

  ```lean
  noncomputable def lowerGroupCard (i : ℕ) : ℕ := Nat.card (lowerGroup R G i)

  noncomputable def herbrandPhiRat (u : ℚ) : ℚ :=
    if u ≤ 0 then u
    else ((∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerGroupCard R G i : ℚ)) +
        (u - ⌊u⌋₊) * lowerGroupCard R G (⌊u⌋₊ + 1)) / lowerGroupCard R G 0
  ```
  so `φ(n) = (g_1 + ⋯ + g_n) / g_0` at natural numbers (`herbrandPhiRat_natCast`), `φ` is linear of
  slope `g_{m+1}/g_0` on `[m, m + 1]` (`herbrandPhiRat_segment`), and for finite `G` it is
  positive on positive arguments, strictly increasing and bijective
  (`herbrandPhiRat_strictMono`, `herbrandPhiRat_bijective`).
- The inverse: `herbrandPsiRat R G = Function.invFun (herbrandPhiRat R G)`, with
  `herbrandPhiRat_herbrandPsiRat`, `herbrandPsiRat_herbrandPhiRat`, monotonicity, the comparison
  lemmas `herbrandPsiRat_le_iff : ψ v ≤ u ↔ v ≤ φ u` (and `<`, `≥` forms) and the explicit value on
  a segment `herbrandPsiRat_segment`.
- Upper groups. For `v : ℚ`, `upperGroupRatIndex R G v = sInf {n : ℕ | v ≤ φ(n)}` and

  ```lean
  noncomputable def upperGroupRat (v : ℚ) : Subgroup G :=
    lowerGroup R G (upperGroupRatIndex R G v)

  theorem upperGroupRat_eq_ceil_herbrandPsiRat [Finite G] (v : ℚ) :
      upperGroupRat R G v = lowerGroup R G ⌈herbrandPsiRat R G v⌉₊
  ```
  with `G^v = G_0` for `v ≤ 0`, `G^{φ(n)} = G_n` (`upperGroupRat_herbrandPhiRat_natCast`), the
  groups decreasing in `v`, and `G^v = G_{m+1}` for `φ(m) < v ≤ φ(m + 1)`.
- The compatibility of upper groups with a quotient, as a proposition: for a normal subgroup `H`
  and a local ring `S` with an action of `G ⧸ H`,

  ```lean
  def UpperGroupRatQuotientCompat (S : Type*) [CommRing S] [IsLocalRing S]
      (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
    ∀ v : ℚ, 0 ≤ v →
      (upperGroupRat R G v).map (QuotientGroup.mk' H) = upperGroupRat S (G ⧸ H) v
  ```
  It is proved in `Herbrand/RationalQuotient.lean` and `Herbrand/LowerQuotient.lean`.

## Proofs

All by computation with the explicit formula: positivity of the `g_i` (each group contains `1`)
gives strict monotonicity, by comparing the sums and the fractional terms on the same or on
different unit intervals; surjectivity solves the linear equation on the segment
`[m, m + 1]` with `φ(m) < v ≤ φ(m + 1)`, the index `m + 1` being `upperGroupRatIndex R G v`, which
exists because `φ(n) ≥ n / g_0` is unbounded. The statements on `ψ` follow from `φ` being an order
isomorphism; `⌈ψ(v)⌉ = upperGroupRatIndex R G v` because `m < ψ(v) ≤ m + 1` on that segment.

## Declarations

In the order of the file: `lowerGroupCard`, `lowerGroupCard_pos`, `one_le_lowerGroupCard_cast`,
`lowerGroupCard_of_subsingleton`, `herbrandPhiRat`, `herbrandPhiRat_of_nonpos`,
`herbrandPhiRat_zero`, `herbrandPhiRat_of_pos`, `herbrandPhiRat_natCast`, `herbrandPhiRat_nonneg`,
`herbrandPhiRat_pos`, `herbrandPhiRat_strictMono`, `herbrandPhiRat_monotone`,
`herbrandPhiRat_injective`, `exists_natCast_le_herbrandPhiRat`, `herbrandPsiRat`,
`herbrandPsiRat_herbrandPhiRat`, `herbrandPsiRat_zero`, `upperGroupRatIndex`, `upperGroupRat`,
`upperGroupRatIndex_of_nonpos`, `upperGroupRatIndex_zero`, `mem_upperGroupRat`,
`upperGroupRat_of_nonpos`, `upperGroupRat_zero`, `upperGroupRat_zero_eq_ker`,
`upperGroupRat_le_zero`, `le_herbrandPhiRat_upperGroupRatIndex`, `upperGroupRatIndex_le`,
`upperGroupRatIndex_monotone`, `upperGroupRat_antitone`, `upperGroupRatIndex_herbrandPhiRat_natCast`,
`upperGroupRat_herbrandPhiRat_natCast`, `UpperGroupRatQuotientCompat`, `herbrandPhiRat_natCast_succ`,
`herbrandPhiRat_segment`, `herbrandPhiRat_segment_solve`, `herbrandPhiRat_surjective`,
`herbrandPhiRat_bijective`, `herbrandPhiRat_herbrandPsiRat`, `herbrandPsiRat_rightInverse`,
`herbrandPsiRat_leftInverse`, `herbrandPsiRat_strictMono`, `herbrandPsiRat_monotone`,
`herbrandPsiRat_injective`, `herbrandPsiRat_surjective`, `herbrandPsiRat_bijective`,
`herbrandPsiRat_le_iff`, `le_herbrandPsiRat_iff`, `herbrandPsiRat_lt_iff`, `lt_herbrandPsiRat_iff`,
`herbrandPsiRat_of_nonpos`, `herbrandPsiRat_nonneg`, `herbrandPsiRat_pos`, `herbrandPsiRat_segment`,
`upperGroupRatIndex_eq_zero_iff`, `upperGroupRatIndex_eq_succ_iff`, `upperGroupRatIndex_eq_iff`,
`upperGroupRat_of_lt_of_le`, `upperGroupRat_eq_of_segment`,
`upperGroupRatIndex_eq_ceil_herbrandPsiRat`, `upperGroupRat_eq_ceil_herbrandPsiRat`.

## Source and licence

Adapted from two files of the Anthropic Lean formalisation of Fermat's Last Theorem (commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`; registered literature
`anthropic-flt-complete-lean-source-6e837e75`):

| FLT file | SHA-256 |
| --- | --- |
| `Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup.lean` | `d0f2deb5720a630198c7889503957bbe89900eb2d047088dd49953f64a253da0` |
| `Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi.lean` | `ac2a05e1808f08e38eea156dec4f7f4f6f6d1861b7c10a44dde4be8c5dbadc1e` |

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`,
`NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. The FLT `ATTRIBUTION.md` does not
list these files as containing third-party material. The Lean file begins with an attribution
header stating that it was modified.

Changes against the FLT files:

- The two files are one module; statements are on `lowerGroup`. Upstream's
  `IsLocalRing.lowerRamificationCard`, `herbrandPhi`, `herbrandPsi`, `upperRamificationIndex`,
  `upperRamificationGroup`, `UpperRamificationQuotientCompat` are `lowerGroupCard`,
  `herbrandPhiRat`, `herbrandPsiRat`, `upperGroupRatIndex`, `upperGroupRat`,
  `UpperGroupRatQuotientCompat` in `Langlands.Ramification`, and the lemma names follow the same
  replacement. The suffix `Rat` keeps them apart from the Library's real functions: inside
  `namespace Langlands.Ramification.Padic` an unqualified `herbrandPhi` must keep meaning
  `Padic.herbrandPhi`.
- The `ValuationSubring` versions, the example blocks and the `#print axioms` checks are not
  kept. No options are set; the FLT file raised `maxHeartbeats` to 1,000,000 for
  `herbrandPhi_strictMono`, which compiles within Lean's default limit.
- The deprecated `if_pos`/`if_neg` in `herbrandPhiRat_of_nonpos`/`herbrandPhiRat_of_pos` are
  replaced by `ite_eq_left`/`ite_eq_right`.

## Literature

Serre, *Local Fields*, GTM 67 (1979), Chapter IV, §3: the function
`φ(u) = ∫_0^u dt / (G_0 : G_t)`, piecewise linear with slope `g_{m+1}/g_0` on `[m, m + 1]`
(printed page 73, with Proposition 12), its inverse `ψ` (Proposition 13, printed pages 73–74),
and the upper numbering `G^v = G_{ψ(v)}` (printed page 74). Serre's `φ` lives on `[-1, ∞)` with real
arguments and `G_u` for real `u`; here the arguments are rational and `G^v` is `G_⌈ψ(v)⌉`.
