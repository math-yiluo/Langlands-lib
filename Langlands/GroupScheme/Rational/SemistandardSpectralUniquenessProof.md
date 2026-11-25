# Uniqueness of intrinsic semistandard triples from their parabolics

`Langlands.GroupScheme.semistandardSpectralUniqueness` proves exactly
the published `Langlands.GroupScheme.SemistandardSpectralUniquenessStatement.{u}`.
Its provenance is an internal deduction from the theorems identified below.
The target originates in
Waldspurger (2003), I.1, printed pp.238–239, as documented in
`SemistandardSpectralIndex.md`. This module makes no new translation of the
original literature.

`SemistandardSpectralIndex.ofCocharacter_eq_of_parabolic_eq` proves that two
cocharacters of the same fixed maximal split torus giving the same actual
parabolic give the same entire intrinsic triple. The published
`RelativeRoot.nonnegative_rootSupport_of_parabolic_le` applied in both
directions recovers agreement of nonnegative pairings on every actual relative
root. The published `relativeRootNegation` supplies the opposite roots, so the
nonpositive pairings agree too. Integer order then recovers agreement of zero
and positive pairings. The published `relativeRootSignsDetermineDynamic`
identifies both centralizers and unipotent radicals on every test scheme.
`ofCocharacter_eq` gives equality of the intrinsic indices.

`semistandardSpectralUniqueness_of_dynamicCoverage` reduces the exact intrinsic
uniqueness statement to the exact fixed-torus dynamic coverage statement.
It realizes each intrinsic triple by a cocharacter of this same torus, extracts
equality of their actual parabolics by projecting the equality of the parabolic
subtypes, and applies the preceding result.

The final theorem discharges that premise using the exact theorem
`semistandardSpectralDynamicCoverage` in
`SemistandardSpectralDynamicCoverageProof`. That proof recognizes the supplied
representative as a rational Levi using its all-test decomposition, realizes
the given parabolic and Levi simultaneously by an ambient cocharacter, factors
that same cocharacter through the fixed maximal split torus, and identifies the
supplied geometric radical with its dynamic radical. Its paired Markdown gives
the declaration-level structural dependencies. It does not assume the present
uniqueness theorem. Thus the final theorem has no extra dynamic realization or
uniqueness premise.

The route preserves arbitrary fields, arbitrary universe `u`, connected
reductivity, and maximality of the given split torus. The subgroup equalities
are all-test equalities, with no quotient by presentations or conjugacy.
The target pair and all of its imported pairs are unchanged.
