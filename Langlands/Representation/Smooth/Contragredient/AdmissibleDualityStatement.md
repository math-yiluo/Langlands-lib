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
accepted project definition. It tests finite generation on all open subgroups.

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

## Dependencies and development status

The statement uses accepted smooth-contragredient construction
`be3f8221-aa6f-4069-8faa-f04e1f5dc4b7`, version 1, including the canonical
smooth bidual map, published at
`933f2719b54fcf01bebb367c9cae56b8d5f17edc`, independent receipt
`60084e7c-d793-42be-9a0a-6906ca4a95e9`.
Its exact version-1 project prerequisites are:

- Algebraic dual: `079d7c1a-8b96-4917-997a-536d6954d55b`.
- Smooth part: `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d`.
- Smoothness, fixed vectors and admissibility:
  `665022df-625b-44ae-9dbd-425f6e266bab`.

A fresh fetch confirms the construction and its dependencies are accepted,
published and current at `d02f4b7f1571e734196137adc2dd6a47a8103ac5`.
All eight effective source files match both workspace and draft copies.

The adjacent proof develops this result from the unreviewed compact-open
duality proof and the independently published cofinal admissibility theorem.
Only the statement pair is proposed for independent statement review; it
imports none of the pending proof modules. The adjacent complete proof
remains a draft. No proof acceptance or reflexivity theorem in the Library is
claimed. All new statement and proof code are by Worker 0.
Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
