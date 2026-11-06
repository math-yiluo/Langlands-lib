# Pole orders at `s = 0` of pairs of segment representations

This module defines the contragredient segment `Δ^∨` of a segment `Δ`. It then
computes the order of the pole at `s = 0` of `L(s, St(Δ) × St(Δ'))` for two
segments `Δ` and `Δ'` in the same universe. Here `St(Δ)` is any
representation in the Library relation `IsSegmentHead Δ`, that is, the
irreducible head of `i(ρ, νρ, …, ν^(m-1) ρ)`. The pole order is `1` if
`SegmentPoleLink Δ Δ'^∨` holds and `0` otherwise. `SegmentPoleLink` is the
link relation of the module `PoleOrderSegmentCombinatorics` (accepted
candidate f6e935c5 of Worker 1702).

The pole-order result is conditional. It takes four hypotheses:

- the Library's unproved `SegmentHeadLFactorStatement`, which states
  Henniart 2002, §2.6;
- `SupercuspidalUnequalRankLFactorStatement`, which states JPSS 1983,
  Proposition (8.1)(i);
- `SupercuspidalEqualRankLFactorStatement`, which states JPSS 1983,
  Proposition (8.1)(ii);
- the Whittaker type of every irreducible supercuspidal representation.

The Library has no statement of the last fact, so it is an explicit hypothesis
`hW`.

## Provenance

Derived.

- Henniart, *Une caractérisation de la correspondance de Langlands locale pour
  GL(n)*, Bull. SMF 130 (2002), §2.6, printed page 595. For irreducible
  supercuspidal `ρ`, `ρ'` this section gives
  `L(s, St_n(ρ) × St_n'(ρ')) = ∏_j L(s, ν^(n+n'-1-j) ρ × ρ')`, with `j` from `1`
  to `min(n, n')`.
- The definition `Segment.dual` is internal: `Δ^∨ = [ν^(1-n) ρ^∨, ρ^∨]` is the
  set of contragredients of the members of `Δ = [ρ, ν^(n-1) ρ]`
  (`mem_support_dual_iff`). The module does not relate the contragredient of
  `St(Δ)` to `Δ^∨`; it uses `Δ^∨` only to express the pole condition.
- Henniart 2002, §4.2, printed page 599. The pole order `v(τ, m)` at `s = 0` of
  `L(s, σ ⊗ τ ⊗ St_m)` counts the pairs `(ρ, n)` for which some
  `j ∈ {1, …, min(m, n)}` has `ν^(m+n-1-j) ρ ≃ τ^∨`. The main theorem here is
  the corresponding statement for a single pair of segments on the
  representation side.
- JPSS 1983, Proposition (8.1), printed page 443. It computes each factor
  `L(s, ν^c ρ × ρ')`. The factor is `1` if the ranks differ ((8.1)(i)). For
  equal ranks it has a simple pole at `s = 0` exactly when `ν^c ρ ≃ ρ'^∨`
  ((8.1)(ii), through the accepted module `SupercuspidalPairPoleOrder`).

The rewriting of the `j`-condition as `SegmentPoleLink Δ Δ'^∨` uses the
integral-twist freeness of supercuspidal classes
(`Classification.cuspidalIntegralTwistFreeness`). It is internal to this
formalization. Henniart instead rewrites the condition through the differences
`w(τ, m)` of §4.2.

## Contents

### The contragredient segment (namespace `PadicField.TopologicalData.Segment`)

- `dual Δ`: the segment with beginning `dualDatum Δ.last` (the cuspidal datum
  of the contragredient of the end `ν^(m-1) ρ` of `Δ`) and the same length
  `m`. It is the selected declaration of the candidate.
- `dual_length`, `dual_rank`, `dual_degree`, `dual_base`: the length, rank and
  degree of `Δ^∨` are those of `Δ`, and its beginning is `dualDatum Δ.last`
  (all by `rfl`).
- `dualDatum_member`: `(ν^i ρ)^∨ = ν^(-i) ρ^∨`, by `dualDatum_twist`.
- `member_dual`: the member `i` of `Δ^∨` is `ν^(i-(m-1)) ρ^∨`.
- `member_dual_of_lt`: for `i < m`, the member `i` of `Δ^∨` is the
  contragredient of the member `m - 1 - i` of `Δ`.
- `mem_support_dual_iff`: `ρ ∈ supp Δ^∨` exactly when `ρ^∨ ∈ supp Δ`. This
  follows from `member_dual_of_lt` and `dualDatum_dualDatum`.
- `dual_last`: the end of `Δ^∨` is `(base Δ)^∨`.
- `dual_dual`: `(Δ^∨)^∨ = Δ`, by the Library lemma `Segment.ext_of_base_length`.

### Counting the `j`-condition (namespace `RankinSelberg`)

- `sum_ite_eq_ite_exists`: a finite sum of the indicators of pairwise
  exclusive conditions `P i` is the indicator of `∃ i, P i`.
- `exists_twist_eq_dualDatum_iff_segmentPoleLink`: let `n` be the length of
  `Δ`, `n'` that of `Δ'`, and `ρ` the beginning of `Δ`. Some
  `j < min(n, n')` has `ν^(n+n'-2-j) ρ = (base Δ')^∨` exactly when
  `SegmentPoleLink Δ Δ'^∨` holds, that is, when `base Δ'^∨ ∈ supp Δ` and
  `last Δ ∈ supp Δ'^∨`. The Lean index `j` is Henniart's `j - 1`. In the
  forward direction, if `(base Δ')^∨ = ν^c ρ` then `Δ'^∨` has integral
  coordinates `[c - n' + 1, c]` over `ρ`, and both memberships become
  inequalities between integers (`HasIntegralCoordinates.twist_mem_support_iff`).
  In the converse direction, `base Δ'^∨ = ν^i ρ` with `i < n` gives
  `(base Δ')^∨ = ν^(i+n'-1) ρ`, and one takes `j = n - 1 - i`.
- `sum_ite_twist_eq_dualDatum`: the sum over `j < min(n, n')` of the
  indicators `[ν^(n+n'-2-j) ρ = (base Δ')^∨]` is
  `if SegmentPoleLink Δ Δ'^∨ then 1 else 0`. At most one `j` satisfies the
  condition, by injectivity of integral twists (`integralTwist_injective`).
  The two previous lemmas then give the result. The `if` uses classical
  decidability (`open Classical in`).

### L-polynomials of arbitrary rank

- `IsPadicRankLPolynomial.ne_zero`: an L-polynomial of a pair of arbitrary
  ranks is nonzero. Its constant coefficient is `1`
  (`IsPadicSymmetricLPolynomial.coeff_zero`).
- `IsPadicRankLPolynomial.congr_equiv`: the relation `IsPadicRankLPolynomial`
  is invariant under representation equivalences of either argument, by
  `IsPadicSymmetricLPolynomial.congr_equiv`. The pole-order theorem does not
  use this lemma. It is included for the summation over the blocks of a
  Langlands datum in the later step of the task.

### Supercuspidal pairs and segment pairs

- `nonempty_equiv_smoothContragredient_iff`: two supercuspidal objects `X`
  and `Y` of `GL_n(F)` satisfy `X ≃ Ỹ` exactly when the class of `X` equals
  the class of `dualRep Y`, the supercuspidal object of the smooth
  contragredient.
- `lPolynomialPoleOrderAtZero_of_cuspidalData`: assume (8.1)(i) and (8.1)(ii)
  in the universe triple `{uF, uV, uV}`, and `hW`. Let `X` and `Y` be
  supercuspidal representatives of cuspidal data `ρ` and `ρ'`. Then every `Q`
  with `IsPadicRankLPolynomial F ψ ν.val X Y Q` has
  `lPolynomialPoleOrderAtZero Q = if ρ = ρ'^∨ then 1 else 0`. If the ranks
  differ, `ρ ≠ ρ'^∨` because `dualDatum` preserves ranks. In that case (8.1)(i),
  applied with the supercuspidal representation of larger rank first (the
  convention of `IsPadicSymmetricLPolynomial`), makes `Q = 1`, whose pole order
  is `0`. For equal ranks, `lPolynomialPoleOrderAtZero_of_supercuspidalEqualRank`
  gives `contragredientIndicator F X Y`. Its condition `X ≃ Ỹ` is identified
  with `ρ = ρ'^∨` by the previous lemma and `dualRep_represents`.
- `lPolynomialPoleOrderAtZero_of_segmentHeads` (main theorem): assume
  `SegmentHeadLFactorStatement`, (8.1)(i) and (8.1)(ii) in the universe triple
  `{uF, uV, uV}`, and `hW`. Let `Δ` and `Δ'` be segments in universe `uV`, and
  let `π` and `σ` satisfy `IsSegmentHead Δ π` and `IsSegmentHead Δ' σ`. Then
  every `P` with `IsPadicRankLPolynomial F ψ ν.val π σ P` has
  `lPolynomialPoleOrderAtZero P = if SegmentPoleLink Δ Δ'^∨ then 1 else 0`.
  The proof takes the representatives `A` and `A'` from the two
  `IsSegmentHead` hypotheses. `SegmentHeadLFactorStatement` then gives
  `P = ∏_j Q_j`, with `Q_j` the L-polynomial of `ν^(n+n'-2-j) A × A'`, after
  uniqueness of L-polynomials (`IsPadicRankLPolynomial.unique`). The pole
  order of the product is the sum of the pole orders of the nonzero factors
  (`lPolynomialPoleOrderAtZero_prod`). Each `ν^c A` represents `ν^c ρ` (the
  Library lemma `Classification.SegmentHeadSupport.isRepresentedBy_twistRep`).
  So the previous lemma gives each factor pole order as
  `[ν^(n+n'-2-j) ρ = (base Δ')^∨]`, and `sum_ite_twist_eq_dualDatum` sums them.

No unconditional analytic claim is made.

## Dependencies outside the Library

The module imports `SupercuspidalPairPoleOrder` and `PoleOrderAtZeroArithmetic`
(accepted candidate 8eef2702), and `PoleOrderSegmentCombinatorics` (accepted
candidate f6e935c5 of Worker 1702). These were not yet merged at Library commit
87e695f5. The workspace holds unchanged copies of them.

The definition `Segment.dual` and its length, rank, degree, endpoint and
involution lemmas are reused from
`Langlands.Representation.Classification.SegmentHeadContragredient`; the member
formula uses its `Segment.dual_member`.
