# Reconstruction of unlinked multisegments from cuspidal content

Author: Worker 219.

The theorem `Langlands.Classification.unlinkedCuspidalContentInjectivity`
proves the exact published proposition
`Langlands.Classification.UnlinkedCuspidalContentInjectivity.{uF,uV} F T`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The field and representation-carrier universes stay independent. For all
actual multisegments `a b : T.Multisegment.{uV,uF}`, it proves that if both
are unlinked and `a.cuspidalContent = b.cuspidalContent`, then `a = b`.
Content equality is equality of the published multiplicity-preserving
multisets. Unlinkedness is the published `Multisegment.IsUnlinked`, which
allows nested and repeated segments. The empty multisegment is included.
The theorem has no further hypotheses. Integral twist freeness is supplied
inside the proof by the published theorem
`Langlands.Classification.cuspidalIntegralTwistFreeness`.

## Provenance

Zelevinsky (1980, §9.10) states this uniqueness and describes a
maximal-segment removal algorithm, but omits the combinatorial proof. The
argument here is an internal elementary derivation. It removes one
segment at a time, starting from a left end of the content. It does not
use superlevel sets of the multiplicity function. No external theorem is
newly cited as a proof input.

## Helper lemmas

In namespace `Langlands.PadicField.TopologicalData`:

- `Segment.ext_of_base_length`: a segment is determined by its base and its
  length. It is proved by structure cases.
- `Segment.base_eq_of_left_end`: let a segment's support lie in a set `S`
  and contain `ρ`, with `ρ.twist (-1) ∉ S`. Then the segment begins at `ρ`.
  If `ρ` were member `i + 1`, its `-1` twist would be member `i`, which
  lies in `S`.
- `Multisegment.mem_cuspidalContent_iff`: a datum occurs in the content of
  `a` exactly when it lies in the support of some segment of `a`. It is
  proved by multiset induction with the published `cuspidalContent_cons`
  and `Segment.mem_cuspidalContent`.
  `Multisegment.support_subset_cuspidalContent` restates one direction.
- `Multisegment.cuspidalContent_eq_zero_iff`: only the empty multisegment has
  empty content, because every segment contains its base.
- `Multisegment.IsUnlinked.of_le`: submultisets of unlinked multisegments are
  unlinked.

In namespace `Langlands.PadicField.TopologicalData.UnlinkedReconstruction`:

- `exists_left_end`: assume integral twist freeness. Then every nonempty
  finite multiset `S` of cuspidal data contains some `ρ` with
  `ρ.twist (-1) ∉ S`. Otherwise, starting from any `σ ∈ S`, induction puts
  `σ.twist (-n)` in `S` for every natural number `n`. Freeness, through the
  published `CuspidalDatum.integralTwist_injective`, makes `n ↦ σ.twist (-n)`
  injective. Then the finite set `S.toFinset` would be infinite.
- `exists_longest_at_left_end`: let `ρ` be in the content of `a`, with
  `ρ.twist (-1)` not in it. Some segment of `a` contains `ρ`, so by
  `base_eq_of_left_end` some segment begins at `ρ`. `Multiset.exists_max_image`
  gives a longest segment `Γ ∈ a` with base `ρ`.
- `twist_length_notMem`: assume freeness and that `a` is unlinked. Let
  `Γ ∈ a` be a longest segment beginning at a left end `ρ` of the content.
  Then `ρ.twist (length Γ)`, the datum just past the end of `Γ`, is not in
  the content. Suppose it lies in a segment `Λ ∈ a` as member `i`. Then
  `Λ` has integral coordinates `[len Γ - i, len Γ - i + len Λ - 1]`
  relative to `ρ`, and `Γ` has coordinates `[0, len Γ - 1]`. Three cases
  arise.
  - Negative start: `Λ` contains coordinate `-1`, by the published
    `Segment.HasIntegralCoordinates.twist_mem_support_iff`. This puts
    `ρ.twist (-1)` in the content, which is a contradiction.
  - Zero start: `Λ` begins at `ρ`, and maximality of `Γ` contradicts
    `i < len Λ`.
  - Positive start: the coordinates satisfy the published `IntervalPrecedes`
    criterion: `0 < c`, `c ≤ len Γ`, and `len Γ - 1 < d`. The published
    `HasIntegralCoordinates.precedes_of_intervalPrecedes` then gives
    `Γ.Precedes Λ`, so `Γ` and `Λ` are linked. This contradicts
    unlinkedness.
- `exists_segment_at_left_end` packages the last two lemmas. It gives a
  segment `Γ ∈ a` beginning at `ρ` with `ρ.twist (length Γ)` outside the
  content.
- `eq_of_right_end`: let `a` and `b` have equal content. Let `Γ ∈ a` and
  `Λ ∈ b` have the same base, and suppose each ends at a right end in the
  sense above. Then `Γ = Λ`. If, say, `len Γ < len Λ`, then member
  `len Γ` of `Λ` is `base.twist (len Γ)`. It lies in the content of `b`,
  which is the content of `a`. This is a contradiction. By
  `ext_of_base_length` the two segments are equal.

## Main theorem

The proof uses strong induction on the cardinality of `a`. If `a = 0`,
the content of `b` is zero, so `b = 0` by `cuspidalContent_eq_zero_iff`.

Otherwise `exists_left_end` gives a left end `ρ` of the content. The
content is shared, so `ρ` is a left end for both `a` and `b`.
`exists_segment_at_left_end` gives `Γ ∈ a` and `Λ ∈ b`, both beginning at
`ρ` and ending at right ends, and `eq_of_right_end` makes them equal. By
`Multiset.cons_erase` and `cuspidalContent_cons`, the contents of
`a.erase Γ` and `b.erase Γ` agree after adding the content of `Γ`, so they
are equal by additive cancellation. Both erased multisegments are unlinked
by `IsUnlinked.of_le`, and `a.erase Γ` is strictly smaller. The induction
hypothesis gives `a.erase Γ = b.erase Γ`. Reinserting `Γ` gives `a = b`.

Repeated segments are handled by erasing a single copy of `Γ`, and nested
segments require no special treatment.

## Dependencies and independence

The module imports the unchanged target statement module, the published
`CuspidalIntegralTwistFreenessProof`, and the published
`SegmentIntervalLinkage`. Beyond the target's own project import closure,
the complete recursive project closure adds exactly seven modules:

- `CuspidalIntegralTwistFreenessProof` and `CuspidalIntegralTwistFreenessStatement`;
- `Smooth.Schur.Proof` and `Smooth.Schur.Statement`;
- `LocalField.Uniformizer`;
- `SegmentIntegralCoordinates` and `SegmentIntervalLinkage`.

The first five make up the freeness proof's own audited closure. The last
two import only the freeness statement and Mathlib. They derive elementary
interval facts about segment support and precedence, using an explicit
freeness hypothesis, which this proof discharges with the published
theorem. A search of these seven modules found no segment-product,
exhaustion, quotient-coverage, ordered-conversion, tempered-uniqueness,
square-integrable-classification or regular-exhaustion declaration.
Every input used is a published theorem, not a proposition definition or a
pending proof.
