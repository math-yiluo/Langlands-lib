# Compact averaging: projection and naturality

The proposition `Langlands.Compact.ProjectionAndNaturality` quantifies over an
arbitrary topological group, two arbitrary complex modules without assigned
topologies, two smooth algebraic representations, and an open subgroup whose
underlying set is compact.

It states two properties of the normalized finite-orbit averaging map:

1. It lands in the existing fixed-vector submodule and fixes every vector of
   that submodule. These are exactly the two clauses of `LinearMap.IsProj`.
   In particular it is idempotent and its image is precisely that submodule.
2. Every complex linear intertwiner commutes with averaging. The equality is an
   equality of complex linear maps.

Original source: Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter II: *Smooth representations*, revision June 16, 2019,
Section 1, page 3, normalized projection discussion; page 4, finite-coset formula
in the proof of Proposition II.1.2. Naturality is an explicit internal
consequence of that finite formula and linear equivariance.

Source ID: `casselman-2019-smooth-representations`. Content SHA256:
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Actual file:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The coefficient field is exactly `Complex`, where every nonzero finite
cardinality is invertible. The result uses only the specified compact open
subgroup and smoothness; no local profiniteness or countability assumption is
needed. It does not assert exactness over general coefficient rings.

This file only defines a proposition. Its proof is a separate contribution.
It imports the compact averaging definitions and the accepted smoothness
definitions (`665022df-625b-44ae-9dbd-425f6e266bab`, version 1).
The compact definitions are accepted artifact
`ed385ab4-3443-4345-a7c7-5d91c74940f9`, version 1, effective snapshot
`aad5d14b4a17fc183be073cb292549ca0522d206c40cf3977960e1ddf23caebc`,
published at Library commit `93def8b48b4703317be20fe31714dddf482835a9`.
The prepared environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
