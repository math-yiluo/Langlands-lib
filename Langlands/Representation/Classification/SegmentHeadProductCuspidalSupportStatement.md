# Cuspidal support of an irreducible product of segment heads

Author: Worker 491.

This module states
`Langlands.Classification.SegmentHeadProductCuspidalSupport.{uF,uV} F T`.
It imports the published `SegmentCuspidalContent`, `LanglandsData` and
`SupercuspidalSupport` modules by Lean name. It introduces a proposition
definition, without a proof of that proposition.

## Exact scope

The field is arbitrary: `{p : ℕ}`, `[Fact p.Prime]`,
`F : PadicField.{uF} p`, and a supplied `T : F.TopologicalData`. The field
universe `uF` and the additional carrier universe `uV` are independent.
The proposition installs the topology supplied by `T` and states

```lean
∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
  d.HasSegmentHeads →
  Representation.IsIrreducible d.induced.representation →
  T.IsSupercuspidalSupport d.induced d.multisegment.cuspidalContent
```

The cuspidal data in the segments therefore have carriers
`Type (max uF uV)`. The blocks, their segment inductions, and the output
product all have this same saturated carrier universe, since
`max uF (max uF uV) = max uF uV`. The representations are the Library's
actual smooth complex representations of general linear groups over
`F.Carrier`.

The supplied datum is any finite ordered family of segments whose degrees
sum to `n`, together with blocks of those degrees. Its hypothesis
`HasSegmentHeads` means each supplied block satisfies the existing
`IsSegmentHead` relation for its segment. In particular, that relation
includes an actual supercuspidal representative of the segment base and
a surjective intertwining map from its increasing segment induction to
the block. Existence of heads is not asserted here.

Irreducibility of the induced product is an explicit additional premise,
using `Representation.IsIrreducible` on its underlying representation.
There is no hypothesis of nonlinkage, precedence order, genericity,
finite length, admissibility, or uniqueness of support. The natural number
`n` is unrestricted, including zero and the empty family when their other
conditions hold.

## Content and the support witness

For each segment `Δ`, the imported `Δ.cuspidalContent` records
`Δ.member i` once for every `i : Fin Δ.length`. The imported multisegment
content sums these multisets over every segment occurrence in
`d.multisegment`. Equal members at different indices and repeated
segments retain all their occurrences.

The conclusion uses the existing relational predicate
`T.IsSupercuspidalSupport`. Unfolding it requires a natural number `k`,
an ordering `ρ : Fin k → CuspidalDatum.{max uF uV,uF} T` whose indexed
multiset equals exactly `d.multisegment.cuspidalContent`, and an
`IsCuspidalConstituent` witness for `d.induced`. That witness consists of
the rank-sum equality, actual supercuspidal representatives `A i` of
every `ρ i`, irreducibility of the product, and an actual
`SmoothRep.IsSubquotient` witness from the normalized cuspidal product
`T.cuspidalProductInduced ρ h A`.

Thus proving the proposition must realize the irreducible product as a
subquotient of actual normalized induction of exactly these cuspidal
representatives. The imported rank-sum identities alone do not supply
that witness. No equality involving the noncanonical chosen function
`supercuspidalSupport` and no Grothendieck-group equality is asserted.

## Derived provenance and remaining proof work

The source is A. V. Zelevinsky, *Induced representations of reductive
p-adic groups II. On irreducible representations of GL(n)*, Ann. Sci.
ENS (4) 13 (1980), pp.165–210, literature ID
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The original passages used here were read in the retained PDF:

- §1.1(a,c), printed p.170, PDF p.7, records exactness and induction in
  stages; §1.5(b), printed p.171, PDF p.8, gives the tensor-coordinate
  form of induction.
- §1.10, printed p.174, PDF p.11, defines support by a multiset of
  irreducible cuspidal classes realizing an irreducible subquotient of
  their product. Its support convention was also checked in the page
  image. Its existence, uniqueness, and embedding assertions are
  separate from the present target.
- §9.10, printed p.201, PDF p.38, uses the underlying cuspidal
  multiplicities for products of unlinked special representations.
  That page was also checked visually. Its classification and
  reconstruction argument is motivation, not a proof input here.

No source-specific errata file was found under the current Library's
`notes/errata` or among its Zelevinsky notes. The published
`notes/henniart/gln-classification-sources.md` was consulted for the
source boundary.

This exact proposition is a derived support-realization statement,
not a claim that §9.10 states it verbatim in this generality. Its intended
route extracts the primitive quotient maps already present in the head
relations, proves their normalized product map surjective, and
identifies the nested segment induction with the flattened ordered
cuspidal induction through actual tensor-compatible induction in
stages. The resulting quotient is a subquotient; the explicitly assumed
irreducibility supplies the remaining constituent condition. Actual
preservation of the quotient maps, the tensor and rank transports in
flattening, and the exact multiplicity enumeration all remain proof
obligations. An abstract stages comparison for a composed presentation
does not by itself establish the required tensor-factor comparison.

## Independence

The three direct imports supply the definitions of the datum, heads,
member content, induction, and support, together with lower construction
lemmas. No proposition-valued statement is applied as a proved theorem
in this module.

The support-realization claim is independent of generic segment-product
uniqueness, multisegment exhaustion, ordered strong-head existence,
quotient coverage, ordered conversion, tempered uniqueness,
`SquareIntegrableLanglandsClassification`, square-integrable exhaustion,
and regular exhaustion. It also does not use uniqueness of supercuspidal
support or the all-rank cuspidal-induction association theorem. The
proof successor must audit the direct and transitive dependencies of any
lower results it reuses and preserve these boundaries.
