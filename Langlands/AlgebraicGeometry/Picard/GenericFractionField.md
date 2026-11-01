# A chosen fraction field and the generic point

This internal adapter identifies the spectrum of any chosen fraction field of
a domain with the spectrum of the residue field at the generic point of its
spectrum. The isomorphism commutes with the actual maps to the original
spectrum.

The parameters are a bundled `R : CommRingCat.{u}` with `[IsDomain R]` and
`K : Type u` with `[Field K]`, `[Algebra R K]` and `[IsFractionRing R K]`.
For an unbundled domain `R₀`, use `R := CommRingCat.of R₀`; no choice of a
different fraction-field algebra structure is made.

In namespace `Langlands.AlgebraicGeometry`,
`fractionFieldSpecIso R K` identifies `Spec K` with the spectrum of the
function field of `Spec R`. Its theorem
`fractionFieldSpecIso_hom_fromSpecStalk` states that composition with the
generic stalk map is exactly
`Spec.map (CommRingCat.ofHom (algebraMap R K))`.
`fractionFieldGenericPointIso R K` then identifies `Spec K` with the
spectrum of the residue field at `genericPoint (Spec R)`, and
`fractionFieldGenericPointIso_hom_fromSpecResidueField` gives the same
compatibility with `fromSpecResidueField`. Both equalities also have the
generated reassociated forms.

The construction uses Mathlib's fraction-field uniqueness isomorphism and its
function-field realization as the local ring at the generic point. That local
ring is a field for an integral scheme. Its residue map is therefore injective
and, as a quotient map, surjective. The resulting residue-field isomorphism
gives the required spectrum isomorphism. Algebra-map compatibility proves
the asserted equality with the given spectrum map. The auxiliary theorem
`isIso_genericPoint_residue` proves the residue-map isomorphism for every
integral scheme, by injectivity of a ring map from a field and surjectivity
of the residue quotient.

These definitions are internal categorical and localization adapters for the
two-axis extension task. They require no valuation, rank, noetherianity or
projectivity hypotheses and prove no bundle extension theorem.
Their provenance is the indicated composition of Mathlib's existing
localization and scheme constructions; they do not translate an additional
literature statement.
