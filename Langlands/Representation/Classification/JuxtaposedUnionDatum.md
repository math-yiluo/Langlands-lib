# Actual union datum for a juxtaposed pair

Authors: Worker 167 and Worker 1032.

This is an internal supporting construction for the juxtaposed case of
Zelevinsky Proposition 4.6. It builds an actual union segment and a one-block
segment-socle datum. Its final existence theorem assumes the published
proposition `Classification.SegmentZelevinskyConstituentExistence` explicitly;
it does not prove that proposition or the original product's head or socle.

For this module, `Δ` denotes the earlier segment and `Γ` the later one.
`Segment.juxtaposedUnion Δ Γ` has base `Δ.base` and length
`Δ.length + Γ.length`. The definition itself does not assume linkage.
If `Δ.Precedes Γ` and `Δ.IsJuxtaposed Γ`,
`IsJuxtaposed.base_eq_twist_length_of_precedes` proves
`Γ.base = Δ.base.twist (Δ.length : ℝ)`. Indeed, precedence places the second
lower endpoint `c` between `1` and `Δ.length`. If `c < Δ.length`, the class
at `c` belongs to both supports, contradicting disjointness. The integral
coordinate lemmas use the proved `Classification.cuspidalIntegralTwistFreeness`.

`IsJuxtaposed.union_replacement` then proves
`Γ.IsUnionIntersectionReplacement Δ (Δ.juxtaposedUnion Γ) none`. The union
support is obtained from the integral interval `[0, Δ.length + Γ.length - 1]`;
the intersection is empty by the supplied disjointness. The reversed order of
`Γ` and `Δ` in this replacement relation matches the parent product's convention.
`IsJuxtaposed.union_degree` proves that the union's degree is the sum of both
degrees: the base equality identifies the cuspidal ranks, and multiplication
distributes over the sum of lengths.

`SegmentProductDatum.ofSingleSegment U π hdegree` uses `ofBlockList` on the
singleton actual block `⟨U, π⟩`. Here `hdegree : U.degree = n`. Its length is
one, its segment list is `[U]`, and its sole segment equals `U`.
`ofSingleSegment_hasSegmentSocles` retains supplied `T.IsSegmentSocle U π`.
The definition `ofSingleSegmentInducedEquiv` gives an actual representation
equivalence from the datum's induced representation to the supplied factor
transported along `hdegree`. Its proof eliminates this degree equality, applies
`T.singleBlockNormalizedProductEquiv`, and identifies matrix reindexing along
the reflexive equality with the identity. The accompanying irreducibility lemma
uses `Weil.IsomorphismInvariance.irreducible_iff`.

The final theorem `exists_juxtaposedUnionDatum` takes the explicit constituent
existence hypothesis, an arbitrary datum `d` of length two, precedence of segment
1 before segment 0, and their juxtaposition. It requires no property of the
original supplied blocks. It returns actual `U` and `e` with the replacement
relation with `none`, `List.ofFn e.segments = [U]`, `e.HasSegmentSocles`, and
irreducibility of `e.induced.representation`. It also exposes `U.base` as the
base of original segment 1, `U.length` as the sum of both lengths, `U.degree = n`,
`e.length = 1`, and equality of every segment of `e` with `U`. Strong socle
evidence for the sole block is included in `e.HasSegmentSocles`. The proof
chooses the constituent of `U` supplied by the explicit hypothesis, extracts its
irreducibility from the strong socle relation, and packages the singleton datum.

All declarations preserve independent universes `uF` and `uV`; the original
segment datum is `SegmentProductDatum.{uV,uF}`, and actual representation
carriers have the published universe `max uF uV`. There is no saturation of
the segment universe, no alteration of a published statement, and no assumption
about arbitrary irreducible quotient maps from the two-block product.

The mathematical provenance is an internal derivation from published
constructions. No new literature assertion is used as a proof input.
The imported cuspidal twist-freeness proof was published from task
`67279e36-f3c2-42e3-9302-11729784042e`; its proof uses admissible Schur and the
normalized uniformizer, independently of segment constituents and downstream
classification. Segment interval and replacement lemmas use only this freeness
proposition as specified in their signatures. One-block induction and
irreducibility invariance are general representation constructions. A recursive
check of the 77 project modules in this module's import closure found only
lower local-field, matrix-group, smooth-representation, twist, tensor,
induction, Jacquet-definition, segment-definition and interval infrastructure.
There is no import of reverse-product structure or quotient-Hom proofs, linked
pair reducibility, segment-product criteria, adjacent commutation, gluing,
ordered multisegment existence, exhaustion, quotient coverage, square-integrable
classification, or derivative proofs. `SegmentConstituentStatement` is used
only for the explicit hypothesis; no pending proof is treated as evidence.

This supporting module proves no head identification or unique submodule for
the original two-block product. Those remain obligations of the parent theorem.
