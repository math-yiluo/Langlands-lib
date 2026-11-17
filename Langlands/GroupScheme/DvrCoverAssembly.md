# Base change and composition for finite smooth DVR covers

Worker 336.

This module supplies the actual base morphisms, cover witnesses and
composition construction used to assemble a finite smooth cover. It
proves no unconditional existence theorem: `smoothGenericCover` has the
explicit premise `DvrStableNormalizationStatement`, and `Cover.comp`
requires a previously supplied finite surjective group homomorphism.

## Fraction fields and generic fibres

For a flat surjective morphism `b : Spec R' → Spec R`, with `R'` a domain
and with a chosen fraction field `K` of `R`, `exists_generic_factor`
constructs an actual morphism `Spec (FractionRing R') → Spec K` that
commutes with the maps to `Spec R`. To do so, it writes `b` as the
spectrum of a ring homomorphism. Faithful flatness makes that ring
homomorphism injective. Composing with the injection into
`FractionRing R'` and using the fraction-field universal property then
produces the field homomorphism. The definition `genericFactor` selects
such a morphism, and `genericFactor_fac` records its commuting equation.

The lemmas `affine_generic` and `smooth_generic` show that affineness,
respectively smoothness, of the actual generic fibre of a scheme over
`R` persists on the actual generic fibre after this base change. The
proofs use the commuting equation and the canonical isomorphisms
between iterated pullbacks and pullback along a composite. Both
properties are stable under pullback and composition with isomorphisms.
These helpers do not require the source and target domains to be DVRs.

## Cover data and composition

`Cover G` packages an actual DVR `ring : Type u`, its flat surjective
spectrum morphism `base`, an actual group scheme `group` over that DVR,
and an actual homomorphism `map : group → base*G`. It includes smoothness,
quasi-compactness and separatedness of the group, affineness of its
actual generic fibre over `FractionRing ring`, and finiteness and
surjectivity of the homomorphism's underlying scheme morphism.

Given a flat surjective coefficient map `b`, a finite surjective group
map `q : P → b*G`, and a supplied cover `D : Cover P`, `Cover.comp`
constructs a cover of `G`. Its coefficient map is `D.base ≫ b` and its
covering group is exactly `D.group`. Its group map is the composite of
`D.map`, the base change of `q`, and the inverse of the canonical
comparison between iterated group base change and base change along
the composite. Finiteness and surjectivity are preserved by pullback,
composition and the final isomorphism. All properties of the covering
group itself come directly from `D`. No DVR hypothesis on the earlier
rings is needed for this composition constructor; the final ring is
the DVR carried by `D`.

## The smooth-generic construction

For a flat, separated, locally finite-type and quasi-compact group
scheme `G` over a DVR, with smooth affine actual generic fibre over
`FractionRing R`, `nonempty_cover_of_stable` constructs a `Cover G` from
the explicit proposition `DvrStableNormalizationStatement`.
`smoothGenericCover` selects that cover.

The proof applies stable normalization to the underlying scheme of
`G`. After its DVR base change, the group remains locally of finite
type, quasi-compact and separated; `affine_generic` supplies affineness
of its new actual generic fibre. The constructions and lemmas of
`DvrStableGroup` supply the actual smooth model group, its homomorphism,
and every required geometric property. The smooth-generic hypothesis
is used by the stable-normalization premise. This step supplies no
reduction of a group with a nonsmooth generic fibre.

## Provenance and scope

These are internal constructions from the explicit stable-normalization
interface, the model group construction and Mathlib's fraction-field,
faithful-flatness, pullback and group-object APIs. The `Cover` structure
only records actual witness data for the cover conclusion; its
existence is not assumed as a new axiom. All rings and schemes,
including the final DVR, remain in the arbitrary universe `u`.
