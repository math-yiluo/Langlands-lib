# Pole orders at `s = 0` through essentially square-integrable data

Let `π` be an irreducible quotient of `i(π_1, …, π_r)`, where the `π_i` are
essentially square-integrable and given by an essentially square-integrable
Langlands datum `d` of `GL_(n+1)(F)`. Let each block be a segment head,
`π_i = St(Δ_i)`. Let `ρ` be an irreducible essentially square-integrable
representation of `GL_(t+1)(F)` that is equivalent to a segment head
`St(D)`. This module computes the order of the pole at `s = 0` of
`L(s, π × ρ)`. It is the number of indices `i` with `SegmentPoleLink Δ_i D^∨`.
In the notation of the accepted module `PoleOrderSegmentCombinatorics`
(candidate f6e935c5 of Worker 1702), this number is
`poleLinkCount {Δ_1, …, Δ_r} D^∨`. Here `St(Δ)` is any representation in the
Library relation `IsSegmentHead Δ`, and `D^∨` is the contragredient segment
`Segment.dual` of `Classification/SegmentHeadContragredient`.

The pole-order result is conditional. It takes five explicit hypotheses:

- `h95`: the Library's unproved `SquareIntegrableDataLFactorStatement`, which
  states JPSS 1983, Theorem (9.5), in product form;
- `hSH`: the Library's unproved `SegmentHeadLFactorStatement`, which states
  Henniart 2002, §2.6;
- `h81`: the Library's unproved `SupercuspidalEqualRankLFactorStatement`,
  which states JPSS 1983, Proposition (8.1)(ii);
- `h81i`: `SupercuspidalUnequalRankLFactorStatement`, which states JPSS 1983,
  Proposition (8.1)(i);
- `hW`: every irreducible supercuspidal representation is of Whittaker type
  for the standard character.

The last two hypotheses are kept explicit in this lemma, but the Library
already proves both. The Library theorem
`RankinSelberg.supercuspidalUnequalRankLFactor` proves
`SupercuspidalUnequalRankLFactorStatement`. The Library theorem
`Langlands.supercuspidalKirillov` proves `SupercuspidalKirillovStatement`.
`RankinSelberg.isOfWhittakerType_of_supercuspidalKirillov` turns that
statement, supercuspidality and irreducibility into exactly the conclusion
of `hW`. Here it is applied in carrier universe `max uF uV` to the two fields
of the property of an irreducible supercuspidal object. A user of the main
theorem can therefore discharge `h81i` and `hW` from the Library. Only
`h95`, `hSH` and `h81` remain unproved.

## Provenance

Derived.

- JPSS 1983, Theorem (9.5), printed pages 462-463, in the product form of
  Henniart 2002, §2.8, printed page 596:
  `L(s, π × π') = ∏_(i,j) L(s, π_i × π'_j)` for `π = ∑ π_i` and
  `π' = ∑ π'_j`. The Library states it as
  `SquareIntegrableDataLFactorStatement`.
- Henniart 2002, §4.2, printed page 599. The pole order `v(τ, m)` at `s = 0`
  of `L(s, σ ⊗ τ ⊗ St_m)` is a sum over the segments of `σ`. The main theorem
  here is that sum on the representation side, with the test representation
  `ρ = St(D)`. Each summand is the pole order of one pair of segments,
  computed in the accepted module `SegmentPairPoleOrder` from Henniart 2002,
  §2.6, and JPSS 1983, Proposition (8.1).
- The single-block datum `SquareIntegrableLanglandsDatum.single` and the
  shrinking of block universes are internal. They present the test
  representation `ρ` and the blocks of `d` in the form required by the
  Library statement of (9.5).

## Contents

### Single-block data (namespace `PadicField.TopologicalData`)

- `nonempty_unitaryExponentData`: an irreducible essentially
  square-integrable `ρ` of `GL_n(F)`, `n > 0`, has a real exponent `α` such
  that `ν^(-α) ρ` carries an invariant positive definite Hermitian form. The
  proof applies the proved Library theorem `glSquareIntegrableUnitarity` to
  the square-integrable twist given by essential square-integrability.
- `SquareIntegrableLanglandsDatum.single`: the essentially square-integrable
  Langlands datum of `GL_n(F)`, `n > 0`, with the single block `ρ`. Its shape
  is `CuspidalSupport.LeviAdmissibility.oneBlock n`, and its exponent is a
  chosen one from `nonempty_unitaryExponentData`. The ordering condition on
  exponents holds trivially. It is the selected declaration of the candidate.
- `SquareIntegrableLanglandsDatum.single_isLanglandsQuotient`: the datum
  `single ρ` presents every representation `π` equivalent to `ρ`. Induction
  from the one-block parabolic subgroup is the identity up to equivalence
  (`singleBlockNormalizedProductEquiv` and `castRankEquiv`), so the composite
  equivalence onto `π` is the required surjection, and `π` is irreducible
  because `ρ` is.
- `SquareIntegrableLanglandsDatum.exists_withBlocks_isLanglandsQuotient`: if a
  datum `d` with blocks in universe `max uF uV` presents `π`, then the
  replacement of its blocks by equivalent ones in universe `uV` (the Library
  operation `withBlocks`) still presents `π`. The new blocks are the small
  realizations of the Library theorem `padicIrreducibleSmoothSmallRealization`,
  and the induced representations are equivalent by `withBlocksInducedEquiv`.

### Pole orders (namespace `RankinSelberg`)

- `poleLinkCount_map_univ`: the link count of the multisegment
  `Finset.univ.val.map Δ` of a family `Δ : Fin r → Segment` at `D` is the
  number of indices `i` with `SegmentPoleLink (Δ i) D`, written as a sum of
  indicators. The `if` uses classical decidability (`open Classical in`).
- `lPolynomialPoleOrderAtZero_of_segmentHeads_cast`: the main theorem of
  `SegmentPairPoleOrder` for representations of `GL_n(F)` and `GL_t(F)` with
  `n = deg Δ` and `t = deg Δ'`. The representations are moved to the segment
  ranks along the rank equalities, by `h.symm ▸` on the first argument and by
  `castRank` on the second. The proof substitutes the rank equalities.
- `lPolynomialPoleOrderAtZero_eq_poleLinkCount` (main theorem): assume
  `SquareIntegrableDataLFactorStatement` in the universe triple
  `{uF, uV, uW}`, and `SegmentHeadLFactorStatement`, (8.1)(i), (8.1)(ii) and
  `hW` in the triple `{uF, max uF uV, max uF uV}`. Let
  - `π` be a representation of `GL_(n+1)(F)` in universe `max uF uV`;
  - `d` be an essentially square-integrable Langlands datum with blocks in
    universe `max uF uV` and `d.IsLanglandsQuotient π`;
  - `Δ` be a family of segments in universe `max uF uV` such that, for each
    `i`, `deg Δ_i` is the size of block `i` and `IsSegmentHead Δ_i` holds for
    block `i` of `d`, moved to rank `deg Δ_i`;
  - `ρ` be an irreducible essentially square-integrable representation of
    `GL_(t+1)(F)` in universe `max uF uW`;
  - `D` be a segment in universe `max uF uV` with `deg D = t + 1`, and `σ`
    satisfy `IsSegmentHead D σ`, with `castRank` of `σ` equivalent to `ρ`.

  Then every `P` with `IsLanglandsPairLPolynomial F ψ ν.val π ρ P` has
  `lPolynomialPoleOrderAtZero P = poleLinkCount (Finset.univ.val.map Δ) D^∨`.

  The proof shrinks the blocks of `d` to universe `uV` and realizes `ρ` in
  universe `uW` by small realizations. It presents that realization by the
  single-block datum. The statement (9.5) then gives `P = ∏_i ∏_j Q_(i,j)`,
  where `Q_(i,j)` is an L-polynomial of block `i` of `d` and the block `j` of
  the single-block datum, after uniqueness of `IsLanglandsPairLPolynomial`.
  The pole order of a product of nonzero polynomials is the sum of the pole
  orders (`lPolynomialPoleOrderAtZero_prod`). Each `Q_(i,j)` is also an
  L-polynomial of block `i` of `d` and `castRank σ`, by invariance under
  equivalence (`IsPadicRankLPolynomial.congr_equiv`). So
  `lPolynomialPoleOrderAtZero_of_segmentHeads_cast` gives its pole order as
  `[SegmentPoleLink Δ_i D^∨]`. The single-block datum has one block, so the
  sum over `j` has one term, and `poleLinkCount_map_univ` identifies the sum
  over `i` with the link count.

No unconditional analytic claim is made.

## Dependencies

All imported modules are in Library commit 7c489c8a, and unchanged in Library
commit 6f182f92. They include the accepted modules `SegmentPairPoleOrder`,
`SupercuspidalPairPoleOrder`, `PoleOrderAtZeroArithmetic` and
`PoleOrderSegmentCombinatorics`.
