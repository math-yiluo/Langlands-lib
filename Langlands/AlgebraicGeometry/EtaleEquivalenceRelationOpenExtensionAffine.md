# Affineness of an extended relation

This internal helper concerns the actual open extension constructed in
`EtaleEquivalenceRelationOpenExtension`. For an étale equivalence relation
`E` whose source map is separated, the unit is both open and closed. Its
open complement is therefore closed in `E.R`. If `E.R` is affine, the
complement is affine.

The module constructs an isomorphism from the extended arrow scheme
`V ⊔_{E.U} E.R` to the disjoint union of `V` with this complement.
Consequently the extended arrow scheme is affine if `V` and `E.R` are
affine. All schemes have an arbitrary universe `u`.

The proof is internal derived content: Mathlib's coproduct universal
property for complementary opens decomposes `E.R`; the pushout universal
property then replaces its unit component by `V`. This is the affine-arrow
part of the pushout step in Stacks Project, Proposition 70.8.1, Tag 07SU
(registered source `stacks-noetherian-approximation-2026-11-01`,
`07SU.html`). It does not assert the approximation or comparison steps.

All declarations are in the namespace
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.OpenExtension`.

- `offDiagonalOpen E` is the open complement of `Set.range E.unit`.
  `offDiagonalOpen_isClosed` proves that it is also closed, using the
  openness of the unit.
- `offDiagonalOpen_isClosedImmersion` proves that its inclusion is a
  closed immersion: an open immersion with closed range is closed.
  `offDiagonalOpen_isAffine` consequently proves that this open subscheme
  is affine when `E.R` is affine.
- `isCompl_unit_offDiagonal` identifies the open ranges of the unit and
  of the complement inclusion as complementary opens.
  `offDiagonalCofanIsColimit` applies Mathlib's coproduct universal
  property for complementary open subschemes. Neither declaration needs
  an affine hypothesis.
- `toCoprod E ι` maps `E.R` into
  `V ⨿ (offDiagonalOpen E).toScheme`. On the unit component it is
  `ι` followed by the left coproduct inclusion; on the complement it is
  the right inclusion. The equations `unit_toCoprod` and
  `offDiagonal_toCoprod` prove these formulas, with reassociated simp
  forms. This map and its equations do not require `ι` to be open.
- `arrowsCoprodIso E ι` is the displayed isomorphism when `ι` is an open
  immersion. Its forward map descends from the pushout, using the left
  coproduct inclusion and `toCoprod`. Its inverse is the coproduct descent
  of the enlarged unit and the old complement inclusion. Pushout and
  coproduct extensionality prove the inverse laws; on the old arrow
  scheme one uses `offDiagonalCofanIsColimit` to check both components.
- `arrows_isAffine` transports affineness of the binary coproduct across
  `arrowsCoprodIso`. Its exact hypotheses are that `E.s` is separated,
  `ι : E.U ⟶ V` is an open immersion, and `V` and `E.R` are affine.
  In particular no affineness of `E.U` is assumed.
