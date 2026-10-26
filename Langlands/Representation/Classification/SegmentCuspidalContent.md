# Cuspidal content of segments and multisegments

Author: Worker 328.

This module records every indexed member of a segment in a multiset and sums
these contents over every occurrence in a multisegment. It adds the elementary
membership, cardinality, rank-sum and additivity lemmas to the published
`Langlands.Representation.Classification.Segments` interface.

## Parameters and multiplicities

All declarations lie in `Langlands.PadicField.TopologicalData`, with arbitrary
`p : ℕ`, `[Fact p.Prime]`, `F : PadicField.{uF} p` and supplied
`T : F.TopologicalData`. The field universe `uF` and representation-carrier
universe `uV` are independent. The entries are the existing
`CuspidalDatum.{uV,uF} T`: a positive rank and an isomorphism class of actual
irreducible supercuspidal smooth complex representations of that general linear
group for the topology supplied by `T`.

For `Δ : Segment.{uV,uF} T`, the definition is exactly

```lean
Segment.cuspidalContent Δ =
  (List.ofFn (fun i : Fin Δ.length => Δ.member (i : ℕ)) : Multiset _)
```

Thus it records one occurrence for each index from zero through `Δ.length - 1`.
If two indices have equal members, both occurrences remain. The published
`Segment.support` is Set-valued and forgets these multiplicities.

For `a : Multisegment.{uV,uF} T`, the definition is exactly

```lean
Multisegment.cuspidalContent a = (a.map Segment.cuspidalContent).sum
```

Every occurrence of a segment contributes its entire content. In particular,
repeated segments contribute repeatedly. No order or representative of the
underlying quotient defining a multiset is chosen.

## Elementary lemmas and their proofs

In namespace `Segment`:

- `mem_cuspidalContent Δ ρ` identifies `ρ ∈ Δ.cuspidalContent` with
  `ρ ∈ Δ.support`. The proof changes the `List.ofFn` membership witness
  `i : Fin Δ.length` into the natural-number witness and bound in `support`,
  and conversely.
- `card_cuspidalContent Δ` gives `Δ.cuspidalContent.card = Δ.length`, by the
  length formula for `List.ofFn` and the cardinality of a list viewed as a multiset.
- `sum_rank_cuspidalContent Δ` gives
  `(Δ.cuspidalContent.map CuspidalDatum.rank).sum = Δ.degree`. Every member
  is a twist of `Δ.base`, and the definition of twisting preserves rank. Mapping
  rank over the list therefore yields `Δ.length` copies of `Δ.rank`, whose sum
  is `Δ.length * Δ.rank`, the definition of `Δ.degree`.
- `cuspidalContent_of_length_one Δ h`, for `h : Δ.length = 1`, gives
  `Δ.cuspidalContent = {Δ.base}`. It simplifies `List.ofFn` and uses
  `Segment.member_zero`.
- `cuspidalContent_singleton ρ` specializes this to
  `(Segment.mk ρ 1 Nat.one_pos).cuspidalContent = {ρ}`.

In namespace `Multisegment`:

- `cuspidalContent_zero` gives content zero for the empty multisegment.
- `cuspidalContent_singleton Δ` gives the content of `Δ` for the singleton
  multisegment `{Δ}`.
- `cuspidalContent_cons Δ a` gives
  `cuspidalContent (Δ ::ₘ a) = Δ.cuspidalContent + a.cuspidalContent`.
- `cuspidalContent_add a b` gives
  `(a + b).cuspidalContent = a.cuspidalContent + b.cuspidalContent`.
- `sum_rank_cuspidalContent a` gives
  `(a.cuspidalContent.map CuspidalDatum.rank).sum = a.degree`.

The first four multisegment lemmas follow from multiset map and sum laws. The
last is proved by multiset induction: the empty case is zero, and the cons
case combines additivity, the single-segment rank formula and the definition
`Multisegment.degree a = (a.map Segment.degree).sum`. There is no empty
`Segment`, since the existing structure requires positive length; the zero
formula concerns `Multisegment`.

## Provenance and dependency boundary

This is an internal finite-combinatorial construction from the published
segment data, with proofs by list and multiset identities. Its motivation is
the finite cuspidal multiplicity data appearing in Zelevinsky (1980), §9.10,
printed p.201, one-based PDF p.38. That passage uses a finitely supported
nonnegative integral function on cuspidal classes in its reconstruction
argument. The present module supplies indexed-member multisets; it does not
implement that reconstruction argument or identify representation-theoretic
cuspidal support.

The cited page was read and visually checked in the registered original:

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  pp.165–210.
- Literature ID: `zelevinsky-1980-induced-ii`.
- SHA256: `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- Relevant location: §9.10, printed p.201, PDF p.38.

No source-specific errata note was present in the current public notes at the
time of this reading. The source is motivation for the data, not a proof input
for the elementary lemmas.

The sole direct import is `Segments`. Its transitive project import closure
contains lower-level field, general linear group, smooth representation,
twisting, induction, supercuspidal-class and constituent-relation interfaces.
The proofs here use only the existing segment/member/rank/degree definitions,
`member_zero` and elementary list/multiset facts. They do not depend on generic
segment-product uniqueness, multisegment exhaustion, ordered strong-head
existence, quotient coverage, ordered conversion, tempered uniqueness,
`SquareIntegrableLanglandsClassification`, square-integrable exhaustion or
regular exhaustion. No proposition-valued classification statement is used as
proved input.

No freeness or nonperiodicity of twists, injectivity of member indices,
reconstruction of multisegments, representation classification or uniqueness
of representation-theoretic support is assumed or proved. These remain
separate statement and proof obligations. Consumers with a datum `d` carrying
a multisegment can use `d.multisegment.cuspidalContent` after importing this
module; no change to the datum is needed.
