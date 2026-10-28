# Proof of the finite segment-truncation obstruction

Author: Worker 854.

The theorem `Langlands.Classification.segmentTruncationObstruction` proves
the exact published proposition
`Langlands.Classification.SegmentTruncationObstruction.{uF,uV} F T` from
`Langlands.Representation.Classification.SegmentTruncationObstructionStatement`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The field universe `uF` and the carrier universe `uV` are independent level
parameters of the theorem, and every segment is the actual
`T.Segment.{uV,uF}`. The proof adds no hypothesis. Integral twist freeness
is not assumed: it is the published theorem
`Langlands.Classification.cuspidalIntegralTwistFreeness.{uF,uV} F T`,
reused rather than reproved.

The statement is the combinatorial lemma at the end of Zelevinsky 1980 §9.8,
printed pp.199–200 (registered as `zelevinsky-1980-induced-ii`; resource PDF
pages 36–37). The proof in Lean follows the source argument on printed
p.200, and the endpoint choice and both containment steps are proved on the
actual segments. No errata entry for this lemma was found; the statement's
Markdown records the same search.

## Coordinates on one twist line

All segments are measured on the integral twist line through one cuspidal
datum, using the published `HasIntegralCoordinates Δ ρ a b`: the base of `Δ`
is `ν^a ρ` and `b = a + Δ.length - 1` is the inclusive upper endpoint. The
helpers, in `Langlands.PadicField.TopologicalData.Segment`, are:

- `exists_hasIntegralCoordinates_of_twist_mem`: if `ν^t σ ∈ Δ.support` for
  an integer `t`, then `Δ` has coordinates `[a, a + Δ.length - 1]` on the
  line through `σ`. Write the member as `Δ.member i = ν^t σ` for a natural
  index `i`. Twisting by `-i` gives `Δ.base = ν^(t-i) σ`, so `a = t - i`.
  This lemma is the bridge from natural member indices to integer
  coordinates. `exists_hasIntegralCoordinates_of_mem` is the case `t = 0`.
- `HasIntegralCoordinates.last_eq`: with coordinates `[a, b]`,
  `Δ.last = ν^b ρ`. This follows from the published `member_eq` and the
  definition `last = member (length - 1)`, using `length > 0`.
- `HasIntegralCoordinates.support_subset_or_subset_of_not_isLinked`: let `Δ`
  and `Γ` have coordinates `[a, b]` and `[c, d]` on one line, with
  `c ≤ b + 1` and `a ≤ d + 1`, so the intervals overlap or are juxtaposed.
  If `Δ` and `Γ` are not linked, one support contains the other. If
  `IntervalPrecedes a b c d` (that is, `a < c ≤ b + 1` and `b < d`), the
  published `precedes_of_intervalPrecedes` gives `Δ.Precedes Γ`. That
  includes `Δ.IsLinked Γ`, a contradiction. The opposite configuration gives
  `Γ.IsLinked Δ`, and `IsLinked.symm` gives the same contradiction. With both
  configurations excluded, integer arithmetic gives `c ≤ a ∧ b ≤ d` or
  `a ≤ c ∧ d ≤ b`. The published `support_subset_iff` turns each into a
  support containment. This lemma does both nonlinkage containment steps.

The published `twist_mem_support_iff` (for `ν^k ρ`) and `support_subset_iff`
use the freeness theorem. They make membership and containment on one line
exactly integer interval membership and containment. So equal points on the
line have equal coordinates, and segments on a periodic line never occur.

## The finite endpoint choice

- `finite_setOf_twist_mem_support`: for every `σ` and `Δ`, the set of
  integers `t` with `ν^t σ ∈ Δ.support` is finite. If it is empty this is
  trivial. Otherwise the first helper gives coordinates `[a, b]` on the line
  through `σ`, and `twist_mem_support_iff` puts the set inside `Icc a b`.
  Freeness is essential here: without it, a periodic orbit would give an
  infinite exponent set.
- `finite_setOf_twist_mem_optionalSupport` is the same claim for
  `Option T.Segment`; `none` has empty support.
- `exists_mem_iUnion_optionalSupport_twist_one_not_mem`: for any finite
  index type and possibly empty truncations `A`, a nonempty union
  `U = ⋃ i, optionalSupport (A i)` contains some `ρ` with `νρ ∉ U`. Pick
  `σ ∈ U`. The exponent set `{t : ℤ | ν^t σ ∈ U}` is a finite union of the
  finite sets above, and it contains `0`. `Set.Finite.exists_maximal` gives
  a maximal element `M`. Put `ρ = ν^M σ ∈ U`. If `νρ ∈ U`, then
  `twist_twist` gives `ν^(M+1) σ ∈ U`, which contradicts maximality.

Two more helpers handle the optional truncations. Suppose
`IsTerminalTruncation.exists_of_mem` or `IsInitialTruncation.exists_of_mem`
receives a point of `optionalSupport A`. Then `A` is not `none`, so it is
`some E` for an actual segment `E`. That `E` satisfies `E.support ⊆ Δ.support`
together with `Δ.last ∈ E.support` (terminal case) or `Δ.base ∈ E.support`
(initial case).

## The main argument

Write `U_A` and `U_B` for the two unions in the statement. Suppose, for a
contradiction, that no two of the original segments are linked. `U_B` is
nonempty, and every element of `U_B = ν(U_A)` has the form `νρ` with
`ρ ∈ U_A`, so `U_A` is nonempty. The endpoint lemma, applied with index
type `Fin r`, gives `ρ ∈ U_A` with `νρ ∉ U_A`. Every coordinate below is on
the line through this `ρ`, with `ρ` at coordinate `0` and `νρ` at `1`. This
is how the proof deals with segments on different twist lines: each segment
used contains an integral twist of `ρ`, so the first helper places it on
this line.

1. *`ρ` is the end of `Δ i`.* Some `A i = some E_i` contains `ρ`, with
   `E_i ⊆ Δ i` and `(Δ i).last ∈ E_i`. Give `Δ i` coordinates `[a_i, b_i]`
   and `E_i` coordinates `[c_i, d_i]`. Then `0 ∈ [a_i, b_i]`, `0 ∈ [c_i, d_i]`,
   and `last_eq` gives `b_i ∈ [c_i, d_i]`. If `b_i ≠ 0` then `b_i ≥ 1`, so
   `1 ∈ [c_i, d_i]`, and `νρ ∈ E_i ⊆ U_A`, which is impossible. Hence
   `b_i = 0`.
2. *`νρ` in an initial truncation.* The image equation puts `νρ ∈ U_B`, so
   some `B j = some E_j` contains `νρ`, with `E_j ⊆ Δ j` and
   `(Δ j).base ∈ E_j`. Give `Δ j` coordinates `[a_j, b_j]`, so
   `a_j ≤ 1 ≤ b_j`.
3. *First containment, `Δ i ⊆ Δ j`.* The intervals `[a_i, 0]` and
   `[a_j, b_j]` satisfy `a_j ≤ 0 + 1` and `a_i ≤ b_j + 1`, so the
   nested-or-linked lemma and nonlinkage give a containment. `Δ j ⊆ Δ i`
   would force `b_j ≤ 0`, so `Δ i ⊆ Δ j`, that is `a_j ≤ a_i`. This is the
   source's first step, and it is proved on the actual segments. As in the
   source, the final contradiction does not use it. It is kept so that the
   Lean proof matches the source argument step by step.
4. *The beginning `ρ₁ = ν^(a_j) ρ` of `Δ j`.* `ρ₁ ∈ E_j ⊆ U_B`, so the
   image equation gives `τ ∈ U_A` with `ντ = ρ₁`. Twisting by `-1` gives
   `τ = ν^(a_j - 1) ρ`, the source's `ν⁻¹ρ₁`. Some `A k = some E_k` contains
   `τ`, with `E_k ⊆ Δ k` and `(Δ k).last ∈ E_k`. Give `Δ k` coordinates
   `[a_k, b_k]` and `E_k` coordinates `[c_k, d_k]`. Then
   `a_j - 1 ∈ [a_k, b_k]`, `a_j - 1 ∈ [c_k, d_k]` and `b_k ∈ [c_k, d_k]`.
5. *Second containment, `Δ j ⊆ Δ k`.* The intervals `[a_j, b_j]` and
   `[a_k, b_k]` satisfy `a_k ≤ b_j + 1` and `a_j ≤ b_k + 1`. `Δ k ⊆ Δ j`
   would give `a_j ≤ a_k ≤ a_j - 1`, so nonlinkage gives `Δ j ⊆ Δ k`, that
   is `a_k ≤ a_j` and `b_j ≤ b_k`.
6. *Contradiction.* `c_k ≤ a_j - 1 ≤ 0 < 1 ≤ b_j ≤ b_k ≤ d_k`, so
   `1 ∈ [c_k, d_k]`. Then `twist_mem_support_iff` puts `νρ` in `E_k`, the
   terminal truncation of `Δ k`, so `νρ ∈ U_A`, against the choice of `ρ`.

So some pair `Δ i`, `Δ j` is linked. The case `r = 0`, and the case in
which every truncation is `none`, are covered: there `U_B` is empty, which
contradicts the nonemptiness hypothesis. Repeated segments need no special
treatment.

## Dependencies and independence

The module imports the unchanged target statement and two other Library
modules, and has no other project imports:

- `CuspidalIntegralTwistFreenessProof`, which supplies the theorem
  `cuspidalIntegralTwistFreeness`. It imports its statement module,
  `Smooth.Schur.Proof` and `LocalField.Uniformizer`.
- `SegmentIntervalLinkage`, which supplies `IntervalPrecedes` and
  `precedes_of_intervalPrecedes`. It imports `SegmentIntegralCoordinates`,
  which supplies `HasIntegralCoordinates`, `member_eq`,
  `twist_mem_support_iff` and `support_subset_iff`. That module imports
  only the freeness statement module and Mathlib.

These lower lemmas were checked for meaning: coordinates are inclusive
integer intervals, and membership and containment are stated with the
freeness premise as an explicit hypothesis, which this proof discharges with
the published theorem. The proof does not use
`UnlinkedCuspidalContentInjectivityProof`, `SegmentUnionIntersection` or
`SegmentReplacementInversions`.

The full project import closure, computed recursively from the Library's
import lines, has 55 modules. They are the target and its `Segments`
foundation, the three modules above, and lower foundations: supercuspidal
classes and twists, constituent relations, parabolic and block-factor
induction definitions, Jacquet coinvariants, smooth, admissible, twisted and
unitary representation infrastructure, the admissible Schur theorem, matrix
groups and local-field normalization. A text search of the whole closure
finds none of `GenericSegmentProduct`, `SegmentHeadProduct`,
`MultisegmentHead`, `OrderedMultisegment`, `QuotientExhaustion`,
`SquareIntegrableConversion`, `TemperedBlockUniqueness`,
`SquareIntegrableLanglands`, `RegularLanglands`, `SegmentGeneric` and
`MultisegmentClassification`, and no `sorry` or `axiom` declaration. So the
proof is directly and transitively independent of:

- generic segment-product uniqueness,
- special-head product irreducibility,
- multisegment exhaustion,
- ordered strong-head existence,
- quotient coverage,
- ordered conversion,
- tempered uniqueness,
- square-integrable Langlands classification,
- square-integrable exhaustion,
- regular exhaustion,

and of all their conclusions. The compiled theorem depends only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
