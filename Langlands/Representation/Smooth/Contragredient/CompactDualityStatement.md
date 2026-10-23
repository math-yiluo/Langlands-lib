# Compact-open fixed-vector duality

For a smooth complex representation `rho` of a topological group and a specified
compact open subgroup `K`, restriction from the `K`-fixed smooth dual to the
algebraic dual of the original `K`-fixed space is bijective. The restriction is
the existing linear map `smoothDualFixedRestriction`; bijectivity therefore
asserts an isomorphism of complex vector spaces without choosing a new map.

The group and module have independent universes. The topological-group instance
is quantified inside the proposition. Smoothness, openness and compactness are
explicit hypotheses. There is no topology on the module, no finite dimension,
admissibility, countability, Hausdorffness or global local compactness hypothesis.

## Source and scope

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II, June 16, 2019, Section 3, Proposition II.3.1, page 6, states this
restriction isomorphism. Section 1, Proposition II.1.2, pages 3-4, gives its
averaging decomposition proof. Page 1 specifies the chapter's stronger ambient
locally profinite and countability hypotheses and Noetherian rational
coefficient rings.

This version specializes the coefficients to complex numbers, matching the
implemented averaging construction, and needs only a specified compact open
subgroup. Smoothness makes each orbit under that subgroup finite; a normalized
finite sum therefore gives the needed inverse. No cofinality of compact open
subgroups is assumed. The original source was read, including its ambient
conventions.

Literature ID: `casselman-2019-smooth-representations`.
SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Actual file:
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Dependencies and implemented proof

This module defines the Prop-valued
`Langlands.SmoothDualCompactFixedDualityStatement`. It directly imports
`Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions` and
`Mathlib.Basic.Complex.Basic`. Its transitive project construction imports
supply the smooth contragredient, smooth-part fixed vectors, algebraic dual,
smooth part, and smoothness and fixed-vector definitions. No project proof
module is imported by the statement.

The separate [CompactDualityProof](CompactDualityProof.md) is implemented in
the Library. `Langlands.smoothDualFixedRestriction_bijective` proves bijectivity
of the actual restriction map, and `Langlands.smoothDualCompactFixedDuality`
proves the whole proposition, with the same independent group and carrier
universes and internally quantified topological-group hypothesis.
The proof imports this statement and
`Langlands.Representation.Compact.Definitions`. Its private finite-mean lemmas
show that averaging lands in the fixed space, fixes that space, and is unchanged
by the subgroup action. A fixed functional is determined by its values on
averages, giving injectivity; composing a functional on the fixed space with
averaging gives its fixed smooth extension, giving surjectivity.

The separate compact projection and fixed-vector-surjectivity proofs are also
implemented: `Langlands.Compact.averageMap_isProj` and
`Langlands.Compact.projectionAndNaturality` are in `Compact.ProjectionProof`,
and `Langlands.Compact.fixedVectorSurjectivity` is in
`Compact.SurjectivityProof` (all under `Langlands.Representation`).
The compact-duality proof neither imports those proof modules nor assumes their
conclusions as hypotheses; it establishes the finite-mean properties it uses
locally.

These are statements about implemented, currently published source, not claims
that historical independent acceptance records for compact projection,
surjectivity or compact duality were recovered. Worker 320 checked the
declarations, imports and proof routes against Library
`fb40559309dd366f4145aa31aad8c3db11b7cc07`; the original pre-migration proof
acceptance records were not verified in this correction.
