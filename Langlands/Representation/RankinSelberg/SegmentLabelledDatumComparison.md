# Segment labellings of square-integrable Langlands data

This module connects the Library's square-integrable Langlands data to
multisets of segments, in the form Henniart's §4 uses. Henniart (2002, §§2.6
and 2.8) identifies an essentially square-integrable `π_i` with a segment
`(ρ, n)` through `π_i ≃ St_n(ρ)`, and an irreducible `π` with the multiset of
its square-integrable constituents. His §4 then argues on the multiset of
segments. The module gives three facts for that step: every datum has a segment
labelling; under the square-integrable Langlands classification, two data with
the same multiset of labels have isomorphic irreducible quotients; and a datum
labelled by one segment of length one has only supercuspidal irreducible
quotients. Only the second fact has a hypothesis.

## Provenance

Derived. Henniart's §2.6 (printed p. 595) recalls the bijection
`(ρ, n) ↦ St_n(ρ)` from pairs of a supercuspidal `ρ` and `n ≥ 1` onto the
essentially square-integrable classes. Here `St_n(ρ)` is the unique irreducible
quotient of `i(ρ, νρ, …, ν^(n-1) ρ)` (Zelevinsky [11, 9.3]). The Library
proves this bijection in the form
`Classification.segmentEssentialSquareIntegrableClassification`: an irreducible
representation of positive rank is essentially square-integrable exactly when it
is an `IsSegmentHead` of some segment of that degree. Henniart's §2.8
(printed p. 596) recalls the Langlands classification: the class of
`J(π_1, …, π_r)` determines the multiset `π_1 + ⋯ + π_r` and is determined by
it. The Library states the direction used here as the proposition
`Classification.SquareIntegrableLanglandsClassification`, which is not yet
proved. That is why `nonempty_iso_of_segmentLabelling_eq` takes it as a
hypothesis.

The definitions and statements are internal. They restate Henniart's
identification for the Library's types; Henniart states no lemma of this form.
For a single segment of length one, `St_1(ρ) = ρ`, so the last result is the
Lean form of "a multisegment `{(ρ, 1)}` is the supercuspidal `ρ`".

## Definitions

- `IsSegmentLabelling d Δ`, for a square-integrable Langlands datum
  `d : T.SquareIntegrableLanglandsDatum n` (universe `max uF uV`) and
  `Δ : Fin d.shape.length → T.Segment`: for every block index `i` there is a
  proof `h : (Δ i).degree = d.shape.size i` such that the block `d.blocks i`,
  transported along `h.symm` to `GL((Δ i).degree)`, is an `IsSegmentHead` of
  `Δ i`. The label multiset of a labelling is
  `Finset.univ.val.map Δ : Multiset T.Segment`.

## Results

- `exists_isSegmentLabelling d`: every square-integrable Langlands datum has a
  segment labelling. There is no hypothesis. Each block is irreducible and
  essentially square-integrable by the fields of `d`, so the Library's
  `segmentEssentialSquareIntegrableClassification` gives its segment, and
  `choose` assembles the family.
- `nonempty_iso_of_segmentLabelling_eq hC hn d d' π π' hd hd' Δ hΔ Δ' hΔ' heq`:
  let `hC` be `SquareIntegrableLanglandsClassification`, let `0 < n`, and let
  `π` and `π'` be irreducible quotients (`IsLanglandsQuotient`) of the
  rank-`n` data `d` and `d'`. If `d` and `d'` have segment labellings `Δ` and
  `Δ'` with equal label multisets, then `Nonempty (π ≅ π')`.
- `isSupercuspidal_of_isSegmentHead_of_length_eq_one`: if `Δ.length = 1`, then
  every `IsSegmentHead` of `Δ` is supercuspidal.
  `isSupercuspidal_of_isSegmentHead_cast` is the same statement for a head
  given on `GL(k)` with `Δ.degree = k`.
- `isSupercuspidal_of_segmentLabelling_eq_singleton d π hd Δ hΔ Γ hΓ h`: if
  `π` is an irreducible quotient of `d`, `Δ` is a segment labelling of `d`,
  `Γ.length = 1`, and the label multiset is `{Γ}`, then `π` is supercuspidal.
  There is no hypothesis on the classification.

## Proofs

`nonempty_iso_of_segmentLabelling_eq`. Rewrite both label multisets as
`Multiset.ofFn`. The Library lemma
`Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq` then gives a
bijection `e` of block indices with `Δ' (e i) = Δ i`. The block sizes agree,
since both equal the degree of the common segment. The blocks are isomorphic
after the rank transport by the public lemma
`Classification.TemperedBlockUniquenessReduction.equal_segment_heads_iso`: after substituting the equal segments and
ranks, both blocks are isomorphic to the segment's fixed head, by
`IsSegmentHead.nonempty_iso_segmentHead`. This is exactly the right-hand side of
`hC` for `d`, `d'`, `π` and `π'`, and `hC`'s reverse direction gives the
isomorphism.

`isSupercuspidal_of_isSegmentHead_of_length_eq_one`. An `IsSegmentHead` of `Δ`
comes with a supercuspidal representative `A` of `Δ.base` and a surjective
intertwiner `q` from `T.segmentInduced A.obj Δ.length` onto the irreducible
`π`. For length one, the Library's `segmentInducedOne_supercuspidal` makes this
induced representation irreducible and supercuspidal. The length is substituted
through an auxiliary statement quantified over `m = 1`. The map `q` is nonzero
because `π` has a nonzero vector. It is therefore injective by
irreducibility of the source, hence bijective, and
`GeneralLinear.isSupercuspidal_of_equiv` carries supercuspidality to `π`.

`isSupercuspidal_of_segmentLabelling_eq_singleton`. Comparing cardinalities
gives `d.shape.length = 1`. Let `i` be the unique index
(`singleBlockIndex`); then `Δ i = Γ`, so the block `d.blocks i` is supercuspidal
by the previous result. The Library's `singleBlockNormalizedProductEquiv`
identifies `d.induced` with that block after the explicit rank transport along
`GeneralLinear.reindex (finCongr _)`. The two private lemmas
`isSupercuspidal_rankTransport` and `isIrreducible_rankTransport` move
supercuspidality and irreducibility across this transport, using
`reindex_finCongr_rfl`. So `d.induced` is irreducible and supercuspidal, and
the surjection `d.induced → π` from `hd` is an equivalence as in the previous
proof.

## Use

In the assembly of Henniart's Théorème 1.7(b), the label multisets of the two
data are compared by `multisegment_eq_of_poleLinkCount_eq`
(`PoleOrderSegmentCombinatorics`). Equal multisets then give `π ≃ π'` by
`nonempty_iso_of_segmentLabelling_eq`. The non-supercuspidality hypothesis of
the target excludes the case of one length-one segment, by
`isSupercuspidal_of_segmentLabelling_eq_singleton`.

The identical helper proofs are reused from `Langlands.Representation.Classification.TemperedBlockUniquenessReduction`; their local copies have been removed.
