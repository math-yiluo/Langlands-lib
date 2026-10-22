# The smooth part of an algebraic representation

Worker 0 defines the smooth vectors and their canonical representation
constructions. This pair is unaccepted development. Its only project import is
the accepted foundational smoothness pair; it imports no pending project theorem.

## Mathematical content

Let `R` be a commutative ring, `G` a group with a topology, and `V` an
`R`-module. These types may inhabit independent universes. The representation
space has no topology.

`smoothVectors rho` is the submodule of vectors fixed by some open subgroup.
The defining carrier is exactly `IsSmoothVector rho`. Its construction fields
prove closure directly: the whole group fixes zero, the intersection of two
fixing open subgroups fixes a sum, and a fixing subgroup also fixes a scalar
multiple.

The remaining constructions assume `IsTopologicalGroup G`:

- `smoothSubrepresentation rho` bundles the smooth vectors as Mathlib's
  `Subrepresentation rho`. If `K` fixes `v`, the inverse image of `K` under
  conjugation by `g` inverse fixes `rho(g)v`. This is the open subgroup
  `g K g⁻¹`. The construction field applies the inverse operator to the
  desired equation and uses the original fixing equation.
- `smoothPart rho` is the representation restricted to that submodule, using
  `Subrepresentation.toRepresentation`.
- `smoothInclusion rho` is the subtype inclusion, bundled as an intertwiner.
- `smoothLift hSigma f` restricts the codomain of an intertwiner from a smooth
  representation to the smooth vectors. The codomain-membership field takes a
  fixing subgroup of each source vector and uses equivariance to show it fixes
  the image. No smoothness-transfer theorem is assumed.
- `smoothMap f` restricts an intertwiner to the smooth parts of both modules.
  It applies `smoothLift` to the composite with the source inclusion. The needed
  source-smoothness field retains each subtype vector's fixing subgroup and
  proves the fixing equation by subtype extensionality.
- `smoothEquiv hRho` upgrades the inclusion to a representation equivalence
  when `rho` is smooth. Injectivity is subtype injectivity; surjectivity puts
  every ambient vector into the subtype using `hRho`.

The last constructions allow source and target modules in different universes.
There are no admissibility, finite-generation, local-compactness, characteristic,
or separation hypotheses. The derived properties and universal property have
separate proposition and proof pairs. Intrinsic construction fields are fully
proved here and contain no unproved project assumptions.

## Source correspondence

Casselman, Chapter II, Section 1, page 2, second paragraph, explicitly identifies
the smooth-vector subspace and its stability under the group action, with the
conjugate fixing subgroup. The first paragraph gives the fixing-subgroup
definition. The Lean construction expands these two descriptions directly.
The inclusion, lift, map, and equivalence are internal constructions on this
subspace; they are not attributed to a separately numbered theorem.

- Literature ID: `casselman-2019-smooth-representations`.
- Content SHA:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019, Section 1, page 2, first two paragraphs.
- Actual file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The coefficient and group hypotheses are broader than the ambient setting in
Casselman's chapter. The direct construction-field proofs above justify that
generality without importing averaging, exactness, or finiteness results.

## Exact dependencies and interface

The project import `Langlands.Representation.Smooth.Definitions` is artifact
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1, accepted and published at
commit `10c81beaaff024987cf2945c64d0c9511f6cb686`. Its Lean SHA is
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`.
Independent review receipt: `a26076cd-7da3-4621-992f-5c0207f7fe1e`.

Mathlib supplies `Subrepresentation` and `toRepresentation`, subgroup inverse
images, continuous conjugation, `Representation.inv_apply_eq_iff`,
`LinearMap.codRestrict`, and the equivalence constructor for a bijective
intertwiner. This interface reuses these bundled objects.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Native compilation and axiom inspection succeeded for this pair and its draft
consumers. These checks supply no semantic acceptance or independent proof
receipt.
