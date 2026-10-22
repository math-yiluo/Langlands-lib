# Algebraic laws for subgroup-fixed vector maps

`Langlands.FixedVectorsLawsStatement` is one coherent interface for the maps
and equivalences in [Definitions.md](Definitions.md). It conjoins the following
two explicitly defined proposition clauses in this same Lean module.

`FixedVectorsMapLawsStatement` asserts, in order:

1. An intertwiner carries a subgroup-fixed vector to a vector fixed by that subgroup.
2. The induced linear map evaluates to the original intertwiner.
3. The induced map commutes with the source and target subtype inclusions.
4. Restriction preserves the identity intertwiner.
5. Restriction preserves composition of intertwiners.
6. Restriction of an injective intertwiner is injective.

`FixedVectorsEquivalenceLawsStatement` quantifies two representations, an
equivalence, and a subgroup, and asserts the forward evaluation formula, the
inverse evaluation formula, equality of the underlying linear map with the
restricted intertwiner, and compatibility with inverse equivalences.

The coefficient ring is commutative, the acting object is a group, and the
three representation spaces are additive commutative modules in independent
universes. All representations, intertwiners, equivalences, and subgroups are
quantified inside the clauses. The third module occurs only in the composition
clause. No topology, smoothness, finite generation, Noetherianity, normality,
or admissibility is assumed. No surjectivity assertion for the fixed vectors
of an arbitrary surjective intertwiner is included.

## Provenance

These are Worker 0's internal algebraic consequences of the fixed-vector
condition and the accepted restriction constructions, rather than separately
numbered source theorems. For the fixed-vector condition, see Bill Casselman,
*Introduction to admissible representations of p-adic groups*, Chapter II,
revision June 16, 2019, Section 1, page 2, first paragraph:

- Literature ID: `casselman-2019-smooth-representations`.
- PDF SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Original file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The source's notation means fixedness under every element of the subgroup.
Equivariance preserves that condition, and the restricted maps have unchanged
underlying functions. Identity, composition, injectivity, evaluation, and
inverse compatibility therefore use only the stated algebraic assumptions.

## Exact dependencies

The sole direct project import is
`Langlands.Representation.Smooth.FixedVectors.Definitions`, accepted artifact
`7ad85b8b-caae-4345-ac1b-2c2d551dbb94`, version 1, published and confirmed current
at Library commit `18d2c44b3fecb756a7634ce0f766fdc16b539b45`, with independent
review receipt `7f5084d1-9e75-445b-b031-b754e38c4830`.
Its Lean SHA256 is
`4a80076b02e57bd0cc16a38fb21184ea1fd1d7ad723e240831e6a4625a65aee1`;
its Markdown SHA256 is
`86568444804fbf3b1afae1edb4cc136756c67422b9523ba8fd0e301599384392`.
Its sole transitive project definition dependency is
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1
(`Langlands.Representation.Smooth.Definitions`), as recorded in the accepted
construction's Markdown.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, with Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.
This file defines propositions; their independent proof acceptance is separate.
