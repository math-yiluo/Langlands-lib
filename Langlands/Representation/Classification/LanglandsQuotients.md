# Canonical Langlands quotients and Zelevinsky subrepresentations for `GL_n`

Author: Worker 23.

The published modules `Classification/Segments` and `Classification/LanglandsData`
record the special representations of a segment, the Langlands quotient and
Zelevinsky's representation only through relations on a given representation
`π`, such as `T.IsSegmentHead Δ π` or `d.IsLanglandsHead π`. This module names one
actual representation for each relation. It applies the canonical head and socle
of `Classification/CanonicalConstituents` to the induced representation that the
relation refers to. For each constructor it proves three things:

- the constructor satisfies the relation exactly when some representation does;
- if a representation satisfies the relation, it is isomorphic to the
  constructor in the smooth category;
- if a representation satisfies the relation, so does the constructor.

The module proves no existence. Whether a segment has a head or a socle, and
whether a datum has a Langlands quotient, remain theorems. The constructors are
defined for every input, but they are described only when the relation holds for
some representation.

All definitions live in namespace `Langlands.PadicField.TopologicalData`, for a
p-adic field `F`, a realization `T : F.TopologicalData` (whose topology is used
throughout) and `ν = |det|` with the residue-normalized absolute value.

## Representatives of cuspidal data

- `ρ.representative`, for a cuspidal datum `ρ`, is an actual supercuspidal
  representation in the class `ρ.cls`. It is `Quotient.out ρ.cls`, so it is
  chosen.
- `ρ.isRepresentedBy_representative` proves `ρ.IsRepresentedBy ρ.representative`,
  the published representative relation of `Classification/Segments`.

## Segments

For a segment `Δ` with beginning `ρ`, length `m` and degree `deg Δ = m r`, let `A`
be `Δ.base.representative`. The induced representation `i(A, νA, …, ν^(m-1) A)` is
the published `T.segmentInduced A.obj m`.

- `T.segmentHead Δ` is the smooth head (`SmoothRep.headQuotient`) of this
  induced representation. It is the canonical candidate for `St(Δ)`, Kudla's
  `Q(Δ)`, and Zelevinsky's `⟨Δ⟩^t`.
- `T.segmentSocle Δ` is its smooth socle (`SmoothRep.socleSubrepresentation`). It
  is the canonical candidate for Zelevinsky's `⟨Δ⟩`.

Both have carriers in `Type (max uF uV)` and live on `GL_(deg Δ)(F)`, the setting of
the published relations. The published relations do not depend on the
representative (`isSegmentHead_iff`, `isSegmentSocle_iff`). So the following
theorems hold for the representative chosen here:

- `h.nonempty_iso_segmentHead`, for `h : T.IsSegmentHead Δ π`, gives
  `π ≅ T.segmentHead Δ`;
- `h.isSegmentHead_segmentHead` proves `T.IsSegmentHead Δ (T.segmentHead Δ)`;
- `T.isSegmentHead_segmentHead_iff Δ` states
  `T.IsSegmentHead Δ (T.segmentHead Δ) ↔ ∃ π, T.IsSegmentHead Δ π`.

The socle has the same three theorems: `h.nonempty_iso_segmentSocle`,
`h.isSegmentSocle_segmentSocle` and `T.isSegmentSocle_segmentSocle_iff Δ`.

The underlying objects depend on the chosen representative only up to the
isomorphism `segmentInducedIsoOfRepresented` of the induced representations. The
module does not state this dependence separately. Every statement above concerns
the relations, and those are independent of the choice.

## Segment product data with canonical blocks

For segments `Δ : Fin r → Segment` and `h : ∑ i, deg Δ_i = n`:

- `T.segmentHeadDatum Δ h` is the `SegmentProductDatum` with segments `Δ` and
  blocks `T.segmentHead Δ_i`;
- `T.segmentSocleDatum Δ h` is the same datum with blocks `T.segmentSocle Δ_i`.

`hasSegmentHeads_segmentHeadDatum_iff` proves that the first datum satisfies
`HasSegmentHeads` exactly when every `Δ_i` has a segment head. Dually,
`hasSegmentSocles_segmentSocleDatum_iff` proves that the second satisfies
`HasSegmentSocles` exactly when every `Δ_i` has a segment socle. Precedence
ordering is not changed or asserted. It is a condition on the given order of the
segments.

## Langlands quotients

For a tempered datum `d : T.TemperedLanglandsDatum n`:

- `d.langlandsQuotient` is the smooth head of the standard module
  `i(ν^(u_1) π_1, …, ν^(u_r) π_r)`. It is the canonical candidate for the Langlands
  quotient.
- `d.toLanglandsQuotient` is the quotient morphism from the standard module, and
  it is surjective (`toLanglandsQuotient_surjective`).

For an essentially square-integrable datum `d : T.SquareIntegrableLanglandsDatum n`,
`d.langlandsQuotient` is the head of `i(π_1, …, π_r)`, the canonical candidate for
Henniart's `J(π_1, …, π_r)`. It comes with `d.toLanglandsQuotient` and
`toLanglandsQuotient_surjective`.

For a segment product datum `d : T.SegmentProductDatum n`:

- `d.langlandsQuotient` is the head of `i(π_1, …, π_r)`, with `d.toLanglandsQuotient`
  and `toLanglandsQuotient_surjective`. It is the canonical candidate for Kudla's
  `Q(Δ_1, …, Δ_r)`.
- `d.zelevinskySubrepresentation` is the socle of `i(π_1, …, π_r)`, with the
  inclusion `d.ofZelevinskySubrepresentation`, which is injective
  (`ofZelevinskySubrepresentation_injective`). It is the canonical candidate for
  Zelevinsky's `⟨Δ_1, …, Δ_r⟩`.

The relation `IsLanglandsHead` has the same three theorems in each of the three
forms:

- `h.nonempty_iso_langlandsQuotient` gives `π ≅ d.langlandsQuotient`;
- `h.isLanglandsHead_langlandsQuotient` proves `d.IsLanglandsHead d.langlandsQuotient`;
- `d.isLanglandsHead_langlandsQuotient_iff` states
  `d.IsLanglandsHead d.langlandsQuotient ↔ ∃ π, d.IsLanglandsHead π`.

For segment product data, `IsZelevinskySocle` has the analogous
`h.nonempty_iso_zelevinskySubrepresentation`,
`h.isZelevinskySocle_zelevinskySubrepresentation` and
`d.isZelevinskySocle_zelevinskySubrepresentation_iff`. In the segment form the
relations also contain the conditions `IsPrecedenceOrdered` and `HasSegmentHeads`
(resp. `HasSegmentSocles`) on `d`. The theorems carry these conditions over from
the given `π`, and the constructor satisfies the relation only when `d` meets
them.

## Provenance

This module is derived. Its definitions compose published constructions: the
canonical head and socle of `Classification/CanonicalConstituents`, the induced
representations of `Classification/Segments` and `Classification/LanglandsData`,
and Lean's `Quotient.out`. It makes no new claim from the literature. The sources
call these representations "the unique irreducible quotient" or "the unique
irreducible submodule" of the corresponding induced representation. The
constructors are the representations that satisfy those descriptions whenever any
representation does. The passages are quoted, with page numbers and verified
hashes, in `Classification/Segments.md` (Zelevinsky 1980, introduction and section
9.1; Henniart 2002, section 2.6) and `Classification/LanglandsData.md` (Kudla 1994,
Theorems 1.2.5 and 2.2.2; Henniart 2002, section 2.8; Zelevinsky 1980, Theorem
6.1(a)).

## Universes and scope

The universes are those of the published relations. Tempered and
square-integrable blocks have carriers in `Type uV`. Segment blocks, the induced
representations and all constructors have carriers in `Type (max uF uV)`. Every
p-adic field, every realization, every `n` and every datum is covered.

## Not claimed

The module proves none of the following:

- existence of a segment head or socle, of a Langlands quotient, or of Zelevinsky's
  representation;
- irreducibility of a constructor when the relation fails for every
  representation (the constructor may then be reducible or zero);
- that a segment head is essentially square-integrable;
- uniqueness of the Langlands data, or independence of the ordering of a
  multisegment;
- any classification bijection.
