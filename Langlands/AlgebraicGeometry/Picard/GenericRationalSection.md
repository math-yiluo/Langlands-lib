# Generic residue-field maps as rational sections

For an integral scheme `S` and a morphism `p : X ⟶ S`,
`genericResidueFunctionFieldEquiv p` identifies actual maps from the spectrum
of the residue field at the generic point of `S` with maps from the
spectrum of `S.functionField`. Both sides retain their actual equations
over `S`.

The generic stalk of an integral scheme is a field. Its canonical
residue map is therefore an isomorphism, as proved by the published
`isIso_genericPoint_residue`. The equivalence precomposes a generic
residue-field map with the inverse of the spectrum map of this residue
homomorphism. Its inverse precomposes with the spectrum map itself.
The definition of `fromSpecResidueField` proves compatibility with the
base; cancellation of these inverse spectrum maps proves both inverse
laws.

When `p` is locally of finite type, `genericRationalSectionEquiv p`
composes this change of generic spectrum with Mathlib's
`Scheme.RationalMap.equivFunctionField`, applied to `𝟙 S` and `p`.
Its right side is the subtype of rational maps `S.RationalMap X`
whose composite with `p` equals the rational map of `𝟙 S`. Thus it
expresses rational sections using Mathlib's equivalence classes of
maps defined on dense open subschemes.

These are internal adapters to existing Mathlib constructions. They
do not require separation, noetherianity, or a valuation hypothesis,
and the universe is arbitrary. They do not extend a rational section
to a section on all of `S`, or construct an extending line bundle.
