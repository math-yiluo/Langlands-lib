# The inductive step for the support of segment-head derivatives

This internal helper module is the last of six modules behind the proof of
`Langlands.Classification.SegmentHeadDerivativeSupportTruncation`. It proves
the support bound for every segment from its cases of length one and two
(`headSupportBound_of_base`, restated as the target proposition in
`supportTruncation_of_base`). The two base cases are proved separately in
`SegmentHeadDerivativeSupportLengthTwo` (Worker 256). All declarations live
in the namespace `Langlands.Classification.SegmentHeadSupport`.

Notation. `Δ = [ρ, ν^(m-1) ρ]` is a segment with base cuspidal datum `ρ`,
length `m` and rank `r`, and `ν = |det|`. Its members are
`Δ.member i = ν^i ρ` (definitionally `ρ.twist i`), and its support is
`{ν^i ρ | i < m}`. A *head* of `Δ` is a representation `π` with
`T.IsSegmentHead Δ π`: `π` is the irreducible head of the increasing
induction `ρ × νρ × ⋯ × ν^(m-1) ρ` of some supercuspidal representative of
`ρ`. Write `σ^(d)` for the order-`d` general-linear derivative
`(generalLinearDerivative T ψ N d hd).obj σ`.

## The bound

`HeadSupportBound T Δ` is the target conclusion for one segment. For every
character `ψ`, every head `π` of `Δ`, every `k ≤ Δ.degree` and every
irreducible actual subquotient `σ` of `π^(k)`, there are a multiset `s` and
an optional segment `A` with `T.IsSupercuspidalSupport σ s`,
`Segment.IsTerminalTruncation A Δ` and `{ρ | ρ ∈ s} = Segment.optionalSupport A`.
Its quantifiers, universes and conclusion are those of the target
proposition, after the choice of `Δ`.

## Constituents and heads

- `exists_irreducible_subrepresentation`: a nonzero finite-length smooth
  representation has an irreducible subrepresentation. The lattice of
  subrepresentations is Artinian, hence atomic. An atom is irreducible by the
  published `FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`.
- `exists_irreducible_quotient`: a nonzero finite-length smooth
  representation has an irreducible quotient. The lattice of submodules is
  Noetherian, hence coatomic, and the quotient by a coatom is simple. This
  repeats the argument of the Library lemma
  `SmoothRep.exists_irreducible_quotient_subquotient_of_nonzero`.
- `IsIrreducibleHead.nonempty_equiv_of_quotient`: every irreducible quotient
  of a representation with an irreducible head is equivalent to that head. It
  composes the published `headEquivOfSurjective`, `IsIrreducibleHead.headKernel_eq`
  and `IsIrreducibleHead.nonempty_headEquiv`. The same short argument occurs
  in other Library modules; none of them is imported.
- `isIrreducible_of_isSegmentHead`: a head is irreducible, by definition of
  `IsSegmentHead`.

## Members, windows and terminal truncations

- `twist_natCast_twist`: `ν^j (ν^i ρ) = ν^(i+j) ρ`.
- `twist_natCast_inj`: `ν^i ρ = ν^j ρ` forces `i = j`. It applies the
  published `cuspidalIntegralTwistFreeness` (`ν^a ρ = ρ` only for the integer
  `a = 0`, proved by a central-character argument) to `a = i - j`.
  `member_inj` is the same statement for segment members.
- `window ρ a b` is the set `{ν^j ρ | a ≤ j < b}`. `window_twist` shifts its
  base: `window (ν^c ρ) a b = window ρ (a + c) (b + c)`.
- `tailSegment Δ a` is the segment `[ν^a ρ, ν^(m-1) ρ]` for `a < m`, and
  `tailSegment_support` computes its support as `window ρ a m`.
- `exists_terminal_iff`: a set `S` is the optional support of a terminal
  truncation of `Δ` exactly when `S = window ρ a m` for some `a ≤ m`.
  Forward: for `A = some E`, the base of `E` is some member `ν^a ρ` of `Δ`.
  Twist-freeness makes the members of `E` exactly `ν^(a+i) ρ` with
  `a + i < m`, and the condition `Δ.last ∈ E.support` forces
  `a + E.length = m`. For `A = none`, take `a = m`. Backward: `a < m` gives
  `some (tailSegment Δ a)`, and `a = m` gives `none`.
- `window_of_sides` is the combinatorial core of the step; see below.
- `pos_of_isSupercuspidalSupport`: a nonzero supercuspidal support only
  occurs in positive rank, since every cuspidal datum has positive rank.

## Rank casts and exactness

`rankCast_map_injective`, `rankCast_map_surjective` and `nontrivial_rankCast`
say that rank casts preserve injective and surjective intertwiners and
nontrivial carriers. `preservesShortExact_derivative` restates the published
`generalLinearDerivativeExactness` (Bernstein–Zelevinsky 1977, Proposition
3.2 and §3.5) in the form `PreservesShortExact`.

## Transfer through a product

`support_of_isSubquotient_product` is the following statement. Let `A₀`
represent the cuspidal datum `ρ₀` of rank `r₀`, let `π'` be irreducible of
rank `b`, let `X` be an actual subquotient of the rank cast of `A₀ × π'`, and
let `Q` be a property of multisets. Assume that every irreducible actual
subquotient of every derivative of `π'` has a supercuspidal support `s'` with
`Q s'`. Then every irreducible actual subquotient `σ` of every derivative
`X^(d)` has a supercuspidal support `s` with either `s = ρ₀ ::ₘ s'` and
`Q s'`, or `Q s`. The proof runs as follows.

1. Derivatives are exact, so they preserve actual subquotients
   (`PreservesShortExact.isSubquotient_map`). Hence `σ` is a subquotient of
   `(A₀ × π')^(d)`.
2. `A₀` is irreducible supercuspidal, so its universe lift has the derivative
   pattern (`derivativePattern_of_supercuspidal`). `leibniz_cases` gives two
   cases.
3. If `σ` is a subquotient of `A₀ × π'^(d)`: the published
   `generalLinearDerivativeFiniteLength` shows that `π'^(d)` has finite length,
   because `π'` is irreducible. The functor `A₀ × -` is exact
   (`preservesShortExact_binaryNormalized_sectR`).
   `exists_irreducible_of_isSubquotient_map` then gives an irreducible
   subquotient `τ` of `π'^(d)` with `σ` a subquotient of `A₀ × τ`. The
   hypothesis gives a support `s'` of `τ` with `Q s'`, and
   `isSupercuspidalSupport_cons` gives the support `ρ₀ ::ₘ s'` of `σ`.
4. If `σ` is a subquotient of the rank cast of `π'^(d - r₀)`: the hypothesis
   applies to `σ` directly.

## The two sides

Let `Δ = [ρ, ν^(k+1) ρ]` have length `m = k + 2`. Let `initSegment Δ k` be
`[ρ, ν^k ρ]` and `succSegment Δ k` be `[νρ, ν^(k+1) ρ]`; both have length
`k + 1`. Let `π` be a head of `Δ`, with representative `A` of `ρ`.

`sub_side` assumes the bound for `initSegment Δ k`. It shows that every
irreducible subquotient `σ` of `π^(d)` has a support `s` with either
`s = ν^(k+1) ρ ::ₘ s'` and `{x ∈ s'} = window ρ a (k+1)`, or
`{x ∈ s} = window ρ a (k+1)`, for some `a ≤ k + 1`.

- The published `segmentSpecialConstituentExistence` gives a head `π'` of
  `[ρ, ν^k ρ]`. The published `IsSegmentHead.decreasingSocleEmbedding` embeds
  `π'` into the decreasing induction `ν^k A × ⋯ × A`.
- `X ↦ ν^(k+1) A × X` is exact, so `M = ν^(k+1) A × π'` embeds into
  `ν^(k+1) A × (ν^k A × ⋯ × A)`. By `nonempty_iso_segmentInducedDown_split`,
  this is the decreasing induction `Z` of `Δ`.
- `Z` has finite length by the published `irreducibleProductFiniteLength`, so
  `M` has finite length. `M` is nonzero by the published
  `ProductVanishing.nontrivial_binary`. So `M` has an irreducible
  subrepresentation `τ`. Then `τ` embeds into `Z`, and the published
  `IsSegmentHead.nonempty_equiv_of_down_subrepresentation` gives `τ ≅ π`. So
  `π` is a subrepresentation of `M`.
- `support_of_isSubquotient_product` with `ρ₀ = ν^(k+1) ρ` and `π'` concludes.
  Its hypothesis `Q` comes from the bound for `[ρ, ν^k ρ]`, rewritten by
  `exists_terminal_iff`.

`quot_side` assumes the bound for `succSegment Δ k`. It shows that every
irreducible subquotient `σ` of `π^(d)` has a support `s₀` with either
`s₀ = ρ ::ₘ s'` and `{x ∈ s'} = window ρ (a+1) (k+2)`, or
`{x ∈ s₀} = window ρ (a+1) (k+2)`, for some `a ≤ k + 1`.

- `segmentSpecialConstituentExistence` gives a head `π''` of `[νρ, ν^(k+1) ρ]`
  with representative `νA`. So the increasing induction `νA × ⋯ × ν^(k+1) A`
  maps onto `π''`.
- `X ↦ A × X` is exact, so `A × (νA × ⋯ × ν^(k+1) A)` maps onto
  `M = A × π''`. By `nonempty_iso_segmentInduced_split`, the source is the
  increasing induction `Z` of `Δ`.
- `M` has finite length, as a quotient of `Z`, and is nonzero. So it has an
  irreducible quotient `ω`. Then `Z` maps onto `ω`, and
  `IsIrreducibleHead.nonempty_equiv_of_quotient` gives `ω ≅ π`. So `π` is a
  quotient of `M`.
- `support_of_isSubquotient_product` with `ρ₀ = ρ` and `π''` concludes. The
  windows of `[νρ, ν^(k+1) ρ]` are rewritten with `window_twist`.

## Combining the sides

`window_of_sides` takes `k ≥ 1`, the two descriptions above of two supports
`s` and `s₀` of the same `σ`, and the implication `s ≠ 0 → s = s₀`. It
concludes `{x ∈ s} = window ρ a (k+2)` for some `a ≤ k + 2`.

- If `s = ν^(k+1) ρ ::ₘ s'` with `{x ∈ s'} = window ρ a (k+1)`, then
  `{x ∈ s} = window ρ a (k+2)`.
- If `{x ∈ s} = window ρ a (k+1)` with `a = k + 1`, the window is empty, and
  equals `window ρ (k+2) (k+2)`.
- Otherwise `a ≤ k`, so `ν^k ρ ∈ s`. Then `s ≠ 0`, hence `s = s₀`. Also
  `ν^(k+1) ρ ∉ s` by twist-freeness. Every description of `s₀` contradicts
  this. If `s₀ = ρ ::ₘ s'` with an empty window `s'`, then `ν^k ρ = ρ`,
  so `k = 0`. In the remaining cases `ν^(k+1) ρ` lies in the window of the
  quotient side, so `ν^(k+1) ρ ∈ s₀ = s`.

`headSupportBound_step` proves the bound for `Δ` of length `k + 2`, `k ≥ 1`,
from the bound for all segments of length `k + 1`. It applies `sub_side` and
`quot_side` to the same `σ`. The published `glSupercuspidalSupportUniqueness`
(uniqueness of the supercuspidal support, Zelevinsky 1980, Proposition 1.10)
gives `s = s₀` whenever `s ≠ 0`, because then the rank is positive
(`pos_of_isSupercuspidalSupport`). `window_of_sides` and `exists_terminal_iff`
produce the terminal truncation.

`headSupportBound_of_base` proves the bound for every segment from the cases of
length one and two. It inducts on `n` with `Δ.length = n + 1`, applying
`headSupportBound_step` with `k = n - 1 ≥ 1` for `n ≥ 2`.

`supportTruncation_of_base` restates this as the target: from the bound for
all segments of length one and of length two, it proves
`SegmentHeadDerivativeSupportTruncation.{uF,uV} F T`. The target's
quantifiers are those of `HeadSupportBound` with `Δ` moved to the front, so
the proof only reorders arguments.

## Scope

The module proves only supports. It does not identify a derivative of `π`,
count its irreducible subquotients, give multiplicities, or claim that a
derivative is irreducible or nonzero. The base cases of length one and two
are hypotheses of `headSupportBound_of_base`. The length-two case needs the
reducibility of `ρ × νρ`, which is not proved here.

## Provenance and inputs

The step is an internal argument motivated by the support step of Zelevinsky
1980, §9.8, printed pp.199–200 (registered source `zelevinsky-1980-induced-ii`).
It does not follow the printed proof and does not use Proposition 9.6 or
Theorem 3.5 of that paper. The derivative inputs are general results of
Bernstein–Zelevinsky 1977 (`bernstein-zelevinsky-1977-induced-i`):
exactness of derivatives (Proposition 3.2), the Leibniz filtration
(Corollary 4.14(c)), derivatives of supercuspidal representations (§4.4) and
finite length of derivatives (the published internal finiteness theorem).

Direct imports and the published declarations they supply:

- `Classification.SegmentHeadSupportSplit` (the previous helper modules).
- `Classification.SegmentHeadDecreasingSocle`:
  `IsSegmentHead.decreasingSocleEmbedding`,
  `IsSegmentHead.nonempty_equiv_of_down_subrepresentation`, and through its
  imports `segmentSpecialConstituentExistence`, `isSegmentHead_iff`,
  `headEquivOfSurjective` and `IsIrreducibleHead.headKernel_eq`.
- `Classification.SupercuspidalSupportUniquenessProof`:
  `glSupercuspidalSupportUniqueness`.
- `Classification.CuspidalIntegralTwistFreenessProof`:
  `cuspidalIntegralTwistFreeness`.
- `Classification.IrreducibleProductFiniteLengthProof`:
  `irreducibleProductFiniteLength`.
- `Classification.SegmentTruncationObstructionStatement`: the definitions
  `Segment.IsTerminalTruncation` and `Segment.optionalSupport`. The module's
  proposition definition is not used.
- `Classification.SegmentHeadDerivativeSupportTruncationStatement`: the target
  proposition, for `supportTruncation_of_base`.
- `Derivative.GeneralLinearDerivativeFiniteLengthProof`:
  `generalLinearDerivativeFiniteLength`, `hasFiniteLength_of_isIrreducible`.
- `Derivative.ProductVanishing`: `ProductVanishing.nontrivial_binary`.
- `Category.FiniteIndexRestriction`:
  `FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`.

Module prefixes are `Langlands.Representation.`. The complete closure audit
is in `SegmentHeadDerivativeSupportTruncationProof.md`.

Author: Worker 890.
