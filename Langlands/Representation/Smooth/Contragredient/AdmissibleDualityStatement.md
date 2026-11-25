# Smooth duals of admissible complex representations

Assume that every open subgroup of a topological group contains a compact open
subgroup. The target asserts three compatible properties:

- Smooth functionals separate vectors of every smooth complex representation:
  the canonical smooth bidual map is injective.
- The smooth contragredient of an admissible complex representation is
  admissible.
- The canonical smooth bidual map of an admissible complex representation is
  bijective.

The bidual map is the existing equivariant evaluation map `smoothBidual`.
Bijectivity therefore gives an isomorphism of representations, with its
canonical map specified. Admissibility already includes smoothness in the
project definition. It tests finite generation on all open subgroups.

The group and module universes are independent. The topological-group instance,
compact-open cofinality, smoothness and admissibility are quantified inside the
proposition. No global Hausdorffness, local compactness or countability is
assumed; a concrete group must supply the stated cofinality theorem.
No topology is placed on the complex representation space.

## Source and scope

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II, June 16, 2019, Section 3, page 6:
Proposition II.3.1 identifies compact-open fixed smooth functionals with the
full dual of the fixed vectors. The following paragraph proves preservation
of admissibility. Lemma II.3.2 proves the canonical bidual isomorphism for
admissible representations whose fixed spaces are free over the coefficient
ring. The specialization to complex coefficients makes those finite fixed
spaces free. The injectivity assertion here is a derived strengthening:
ordinary algebraic duals separate arbitrary complex vector spaces, and
compact-open fixed-vector duality extends a separating functional smoothly.
It needs smoothness but not admissibility.

The original page and its ambient conventions were read. We replace the
chapter's locally profinite, countable ambient assumptions by precisely the
compact-open cofinality used in the proof. Establishing that hypothesis for
concrete groups remains separate.

Literature ID: `casselman-2019-smooth-representations`.
SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
Actual file:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

## Dependencies

The statement uses the smooth-contragredient construction of
`Langlands.Representation.Smooth.Contragredient.Definitions`, including the
canonical smooth bidual map, published at
`933f2719b54fcf01bebb367c9cae56b8d5f17edc`.
Its project prerequisites are:

- Algebraic dual: `Langlands.Representation.Dual.Definitions`.
- Smooth part: `Langlands.Representation.Smooth.SmoothPart.Definitions`.
- Smoothness, fixed vectors and admissibility:
  `Langlands.Representation.Smooth.Definitions`.

Inspection found the construction and its dependencies published
at `d02f4b7f1571e734196137adc2dd6a47a8103ac5`.
All eight source files matched the local copies.

The adjacent proof `Langlands.smoothAdmissibleDuality`
(`Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof`)
derives this result from the compact-open duality proof `CompactDualityProof`
and the published cofinal admissibility theorem. The statement imports none
of the proof modules.
Environment: Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
