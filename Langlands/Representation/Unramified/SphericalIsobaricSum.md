# Sphericity of local isobaric sums

`Langlands.Unramified.isSpherical_of_isIsobaricSum` applies to a positive-rank
family of actual irreducible admissible smooth representations of general
linear groups over a p-adic field. Given an actual `IsIsobaricSum` of the blocks,
nonzero spherical fixed vectors in all the blocks imply nonzero spherical
fixed vectors in that sum. The input and output objects use the carrier
universe of the field.

## Proof

Associate to each nonzero uniformizer parameter `z` the singleton segment of
the rank-one unramified character with that value. The scalar-uniformizer norm
of its base is `‖z‖`. A precedence relation from an earlier singleton to a later
one would express the later base as a strictly positive real twist of the
earlier base, decreasing the scalar-uniformizer norm. Sorting parameters by
nondecreasing norm therefore gives a precedence-ordered segment product.

`orderedMultisegmentHeadExistence` provides the strong Langlands head of this
ordered product. `ofCuspidalsInducedIso` and the rank-one character-line
equivalences identify the induced segment product with the actual unramified
principal series. Its spherical irreducible quotient supplied by
`exists_spherical_irreducible_quotient` is isomorphic to the strong head.
Consequently the spherical quotient is a Langlands head of the multiset of
singleton segments. Sorting leaves the spectrum, including multiplicities,
unchanged.

For each spherical block, `sphericalSpectrumExistence` gives its spectrum.
`sphericalConstituentUniqueness` identifies the block with the spherical head
just constructed for that spectrum. `multisegmentHeadClassification` then
identifies the block's supplied label with the multiset of singletons from its
spectrum. Since mapping parameters to singletons commutes with the sum, the
supplied isobaric label is the singleton label of the pooled spectrum. The
same construction gives a spherical head for the pooled spectrum, which is
isomorphic to the supplied sum by multisegment head classification. Transport
its nonzero spherical fixed space along that isomorphism.

## Provenance

This lemma implements the finite-place sphericity step from the proof of
Getz–Hahn Theorem 10.7.5 by combining the Library's segment classification
with its construction and uniqueness of spherical constituents.

| Registered source | PDF SHA-256 | Locator and role |
| --- | --- | --- |
| `getz-hahn-2024-automorphic-representations` | `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507` | (10.33), p. 284 (PDF 296), defines isobaric pooling. Theorem 10.6.3, p. 285 (PDF 297), identifies the isobaric sum of unramified characters with the spherical constituent. The proof of Theorem 10.7.5, p. 288 (PDF 300), uses this for sphericity almost everywhere. |
| `kudla-1994-local-langlands-nonarchimedean` | `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | Theorem 1.2.5(a)–(b), pp. 370–371 (PDF 380–381), gives the segment classification. §2.1, p. 371 (PDF 381), identifies the spherical constituent with the Langlands quotient of the ordered unramified singleton characters and describes exhaustion of spherical objects by such constituents. |
