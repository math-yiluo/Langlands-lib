# Linear maps through the smooth part

Worker 0's `Langlands.smoothHomEquiv` bundles factorization through the
smooth part as a linear equivalence of intertwiner modules:

`Hom_G(rho, sigma) ≃ₗ[R] Hom_G(rho, smoothPart sigma)`.

The coefficient ring is commutative, the group is a topological group, and
the two module carriers may inhabit independent universes. The source
representation `rho` is smooth; the target `sigma` is arbitrary. Neither
module carries a topology. No compactness, admissibility, dimension, or
Noetherian assumption is present.

The forward map is the accepted `smoothLift hRho`; the inverse composes with
the accepted `smoothInclusion sigma`. Both inverse laws and both linearity
fields are proved by intertwiner extensionality and definitional equality.
The membership proofs inside smooth vectors do not change the underlying
maps. No pending unique-factorization theorem is imported.

This is an internal construction on the smooth-vector subspace, useful as
the explicit Hom-space interface for the smooth-part universal property.
It does not introduce a category or claim a separately formalized categorical
adjunction. The adjacent proposition and proof pair give evaluation and
naturality in the source and target.

The source context is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, June 16, 2019, Section 1,
page 2, first two paragraphs: smooth vectors are fixed by open subgroups
and form a stable subspace. This linear Hom-space packaging is internally
derived from those definitions, not attributed to a numbered theorem.
Literature ID: `casselman-2019-smooth-representations`; content SHA
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Actual source:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The sole direct project import is the accepted smooth-part construction,
artifact `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`, version 1, publication commit
`cd8210540c75a7d0a9e2431e4bc9a2535ceaf919`, receipt
`1f969dc8-79b0-4e70-adf8-502752d70c6a`. Its Lean SHA is
`1362c38a196d6657c4d9dd2388e00c77059fc772bdd7f4369e0cbbee19ca4a47`.
Its transitive project dependency is foundational smoothness,
`665022df-625b-44ae-9dbd-425f6e266bab`, version 1. Mathlib supplies the
linear structure on intertwiner modules, composition, and linear equivalences.

Prepared environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
This pair is prepared for independent definition review. Its intrinsic
construction fields are fully proved. Native compilation and axiom inspection
passed, but do not establish independent acceptance.
