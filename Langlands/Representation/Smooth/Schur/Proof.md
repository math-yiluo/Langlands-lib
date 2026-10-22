# Proof of admissible Schur and smooth central characters

`Langlands.admissibleSchur` proves the existing proposition
`Langlands.AdmissibleSchurStatement` in
`Langlands.Representation.Smooth.Schur.Statement`. Worker 189 authored this
proof module. The published statement and its imported project files are
unchanged.

The closing theorem preserves the statement's complete outer parameter order,
with separate universes `uG`, `uV`, and `uW` for the group and the two vector
spaces. Its topological-group instance remains quantified inside the target
proposition. The final unapplied-constant example checks the complete outer
telescope. There is no finite-dimensionality assumption on the entire
representation and no compactness, local compactness, countability, or
semisimplicity assumption.

## Implemented argument

`admissibleSchur_scalarEndomorphism` first obtains nontriviality of the carrier
from irreducibility, using the associated simple group-algebra module. Choose a
nonzero vector and an open subgroup fixing it. Its fixed space is nonzero and,
by admissibility, finite-dimensional over the complex numbers. An intertwining
endomorphism preserves this space. Mathlib's `Module.End.exists_eigenvalue`
and `HasEigenvalue.exists_hasEigenvector` provide a nonzero eigenvector of its
restriction. Consequently the full intertwiner minus that eigenvalue times the
identity is not injective. Mathlib's irreducible-representation alternative
`Representation.IsIrreducible.injective_or_eq_zero` makes this difference zero.
Evaluation on a nonzero vector proves uniqueness of the scalar.

`admissibleSchur_homEquiv` uses a representation equivalence `e` to define the
linear map from the complex numbers to intertwiners sending `c` to `c • e`.
It is injective by evaluation on a nonzero vector. It is surjective because
composition of any intertwiner with `e.symm` is scalar by the preceding lemma.
The inverse of the resulting linear equivalence gives the requested direction.
For the other Hom clause, the closing theorem uses
`Representation.IsIrreducible.bijective_or_eq_zero`: a bijective intertwiner
would construct a representation equivalence, contradicting its assumed
nonexistence. Thus every intertwiner is zero. The target representation's
admissibility hypothesis is retained in the target, although the argument needs
only source admissibility and irreducibility of both representations.

`admissibleSchur_centralCharacter` treats the action of each central element as
an intertwining endomorphism and chooses its scalar. Evaluation on a fixed
nonzero vector proves that these scalars preserve identity and multiplication.
Multiplicativity applied to an inverse pair makes every scalar nonzero, so
`Units.mk0` packages them into a homomorphism to the complex units.

For local constancy, choose an open subgroup `K` fixing a nonzero vector `v`.
For each central element `z`, the set of central `w` with `z⁻¹w ∈ K` is an open
neighborhood of `z`: it is the preimage of `K` under the continuous map
`w ↦ z⁻¹w`. On this neighborhood, `rho(w) v = rho(z) v`. Scalar cancellation
on `v` shows that the character takes the same value at `w` and `z`.
This proves local constancy directly through open neighborhoods. Finally,
evaluation on `v` proves equality with any other character having the stated
action, yielding the required unique existence.

## Source and provenance

The target is the corrected, derived formulation documented in its published
Markdown. The source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter II, *Smooth representations*,
revision June 16, 2019: pages 1–2 for ambient conventions and admissibility,
Proposition II.1.6 on page 4, and Proposition II.2.1 with its preceding
admissibility assumption on page 5. These pages were read in the retained
original PDF.

- Literature ID: `casselman-2019-smooth-representations`.
- PDF SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Retained source: `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The printed II.1.6 omits the hypotheses needed for its Hom formula; this proof
establishes the published target with its explicit irreducibility and
admissibility assumptions. The implemented proof of central scalar action uses
one endomorphism at a time followed by scalar uniqueness, rather than the
source's simultaneous central eigenspace argument. Uniqueness and local
constancy are the derived conclusions justified above. The helper results are
internal steps of this proof, not additional claims attributed verbatim to the
source.

## Dependencies and checking

The only project import is the published Schur statement, which imports the
published smoothness and admissibility definitions. Added Mathlib imports
supply finite-dimensional eigenvectors and algebraic closure of the complex
numbers. The proof uses actual Mathlib intertwiners, representation equivalences,
linear equivalences, and unit-valued monoid homomorphisms.

Development compilation and declaration inspection succeeded in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no warnings. The closing theorem's
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. This
compilation is distinct from exact-target validation, independent semantic
review, and Library publication.
