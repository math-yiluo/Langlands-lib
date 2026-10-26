# Reconstruction of an unlinked multisegment from cuspidal content

Author: Worker 328.

The proposition `Langlands.Classification.UnlinkedCuspidalContentInjectivity`
states that the cuspidal content determines an unlinked multisegment. This
module defines a proposition target; it does not prove it.

## Exact statement and parameters

For arbitrary `p : ℕ`, `[Fact p.Prime]`, `F : PadicField.{uF} p` and supplied
`T : F.TopologicalData`, the definition
`UnlinkedCuspidalContentInjectivity.{uF,uV} F T` is exactly

```lean
∀ (a b : T.Multisegment.{uV,uF}),
  a.IsUnlinked → b.IsUnlinked →
  a.cuspidalContent = b.cuspidalContent → a = b
```

The field universe `uF` and representation-carrier universe `uV` are independent.
The underlying cuspidal data are the published positive-rank isomorphism
classes of actual irreducible supercuspidal smooth complex representations,
using the topology supplied by `T`.

The sole import is
`Langlands.Representation.Classification.SegmentCuspidalContent`. Its
`Segment.cuspidalContent` records one occurrence of `Δ.member i` for each
`i : Fin Δ.length`, and `Multisegment.cuspidalContent` sums these multisets
over every segment occurrence. The hypothesis is equality of these multisets,
including multiplicities. Equality of their underlying sets is not the
hypothesis. The conclusion is equality of the multisets of segments, whose
segment entries record their base cuspidal datum and positive length.

`a.IsUnlinked` is the published condition that no pair of segments belonging
to `a` is linked. In `Segment.IsLinked`, neither support contains the other
and the union of the two supports is the support of a segment. This is not
disjointness of supports: contained, nested and repeated segments are allowed.
There is no nonemptiness condition on `a` or `b`; the empty multisegment is
included. There is no ordering, twist-freeness, interval-model,
support-existence or classification premise.

## Source correspondence and provenance

This is a derived formulation of the finite reconstruction assertion in
A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
pp.165–210, §9.10, printed p.201, one-based PDF p.38.
The registered source is `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.

That passage identifies the absence of linked pairs with minimality among
multisegments of prescribed finite cuspidal multiplicity data and asserts
uniqueness of the minimal element. Its lemma gives an algorithm that removes
maximal segments from the support of the remaining nonnegative integral
function. The original explicitly omits the combinatorial proof. Here the
finite multiplicity function is expressed by the published indexed-member
multisets, and the target is the resulting injectivity assertion. This
translation also requires the actual integral-twist orbit properties of the
cuspidal classes; those properties are not inferred from the names of the
definitions. The universe parameters and the explicit empty case are part
of the present formal formulation.

The cited page was read and visually checked in the registered original, and
its source hash was verified. No source-specific errata note was found under
the current Library's `notes/errata`.

## Proof obligations and dependency boundary

A proof must establish the required integral-twist orbit properties of the
actual cuspidal isomorphism classes, justify their finite interval model, and
prove reconstruction with repetitions retained. One possible combinatorial
route recovers intervals on each free integral orbit from the connected
components of superlevel sets of the multiplicity function. This is a
prospective proof route, not an implemented proof or an additional hypothesis.
Nontriviality of the twisting character alone is not freeness on
isomorphism classes.

The 48-module transitive project import closure of `SegmentCuspidalContent`
was checked against the current Library. All imported Lean/Markdown pairs
are unchanged. It supplies lower-level field, group, smooth representation,
twisting, induction and segment interfaces. This statement has no dependency
on generic segment-product uniqueness, multisegment exhaustion, ordered
strong-head existence, quotient coverage, ordered conversion, tempered
uniqueness, `SquareIntegrableLanglandsClassification`, square-integrable
exhaustion or regular exhaustion. Any proof successor must preserve that
independence and audit every additional dependency.

The target does not assert existence or uniqueness of representation-theoretic
cuspidal support, or a classification of induced representations. Proposition
definitions, source citations and pending proof tasks supply no proof of this
target or of its prerequisites.
