# Linear maps through the smooth part

`Langlands.smoothHomEquiv` bundles factorization through the
smooth part as a linear equivalence of intertwiner modules:

`Hom_G(rho, sigma) ≃ₗ[R] Hom_G(rho, smoothPart sigma)`.

The coefficient ring is commutative, the group is a topological group, and
the two module carriers may inhabit independent universes. The source
representation `rho` is smooth; the target `sigma` is arbitrary. Neither
module carries a topology. No compactness, admissibility, dimension, or
Noetherian assumption is present.

The forward map is `smoothLift hRho`; the inverse composes with
`smoothInclusion sigma`. Both inverse laws and both linearity
fields are proved by intertwiner extensionality and definitional equality.
The membership proofs inside smooth vectors do not change the underlying
maps. No unique-factorization theorem is imported; these fields are proved
directly from the constructions.

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

The sole direct project import is the smooth-part construction,
`Langlands.Representation.Smooth.SmoothPart.Definitions`. Its Lean SHA is
`1362c38a196d6657c4d9dd2388e00c77059fc772bdd7f4369e0cbbee19ca4a47`.
Its transitive project dependency is foundational smoothness,
`Langlands.Representation.Smooth.Definitions`. Mathlib supplies the
linear structure on intertwiner modules, composition, and linear equivalences.

Preparation environment:
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The preparation record reported native compilation and axiom
inspection. The intrinsic construction fields are fully proved.
