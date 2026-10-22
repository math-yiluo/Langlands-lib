# Schur's lemma and central characters for admissible representations

`Langlands.AdmissibleSchurStatement` is one proposition definition with three
related conclusions for an irreducible admissible complex representation:

1. Every equivariant endomorphism is multiplication by a unique scalar.
2. The space of intertwiners to another irreducible admissible representation
   is linearly isomorphic to the complex numbers if the representations are
   isomorphic, and consists only of the zero map otherwise.
3. The center acts by a unique locally constant homomorphism to the complex
   units.

The Lean representation and intertwiner types are Mathlib's actual algebraic
objects. `Representation.IsIrreducible` is Mathlib's abbreviation for a
nontrivial subrepresentation lattice with only bottom and top. In particular,
the zero representation is excluded. Representation equivalence and linear
equivalence in the Hom-space clause are actual equivariant and linear
isomorphisms, each asserted with `Nonempty`; no canonical choice is assumed.
The central character is an actual monoid homomorphism on `Subgroup.center G`,
and its scalar-action equality is asserted for every central element and vector.
No new predicate or construction for central characters is introduced.

The group carries a topological-group structure. The group and the two module
universes are independent. Admissibility uses the accepted all-open-subgroup
definition and includes smoothness. No topology or finite-dimensionality is
assumed on the whole representation space.

## Sources, the printed omission, and the derived scope

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter II, *Smooth representations*, revision June 16, 2019:
Proposition II.1.6, printed/PDF page 4, and Proposition II.2.1 with its preceding
admissibility assumption and proof, page 5. The ambient conventions on page 1
and definitions on page 2 were also read. Pages 4 and 5 were checked visually
against the original PDF.

- Literature ID: `casselman-2019-smooth-representations`.
- Original PDF SHA256:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Actual source:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The printed II.1.6 says only that the two representations are smooth before
giving its one-dimensional-or-zero Hom-space formula. That literal statement
is false, for example for a two-dimensional trivial representation. This
target explicitly requires irreducibility and admissibility and is classified
as a derived, corrected formulation, not a verbatim translation of II.1.6.
The endomorphism clause specifies the scalar isomorphism as well as its
surjectivity. The Hom-space clause translates the displayed formula into
linear isomorphism and zero-map statements.

The correction is justified directly: a nonzero smooth vector lies in a
nonzero finite-dimensional fixed space. Every intertwining endomorphism
preserves that space, and over the complex numbers it has an eigenvector
there. The corresponding eigenspace in the full representation is stable
under the group, so irreducibility makes the endomorphism scalar. A nonzero
intertwiner between two irreducible representations is an isomorphism;
composition with an isomorphism reduces its Hom space to the endomorphism
case. This argument does not require the whole space to be finite dimensional.

Proposition II.2.1 concerns an irreducible admissible representation and states
scalar action of the center. Uniqueness and local constancy are explicit
derived consequences here. Nontriviality makes each scalar unique, the group
law makes the scalar assignment multiplicative and unit-valued, and a
nonzero vector with an open fixing subgroup gives an open kernel in the center.
The resulting character is locally constant. No compactness or countability
of the group is used in these arguments; the retained topological-group
hypothesis suffices for the local-constancy assertion.

These explanations justify the formulation and scope. They do not insert a
proof, axiom, or assumed truth of the target into the Lean file. A separate
proof obligation remains.

## Exact dependencies and status

The only project import is `Langlands.Representation.Smooth.Definitions`,
artifact `665022df-625b-44ae-9dbd-425f6e266bab`, version 1. It is accepted,
published at `10c81beaaff024987cf2945c64d0c9511f6cb686`, and current with no
unavailable dependencies at checked head
`d0f5322f745425b08ae8e72c1031206f45cb049e`. Its Lean SHA256 is
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`;
its Markdown SHA256 is
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.

Mathlib's `RepresentationTheory/Irreducible.lean` supplies the irreducibility
definition and the algebraic nonzero-intertwiner alternative. Its existing
scalar-endomorphism theorem assumes finite dimension of the full space; that
hypothesis is deliberately absent here and is replaced by admissibility.
No pending project proof is imported.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 8 authored this Lean/Markdown pair. Statement review and publication
do not constitute proof acceptance or completion of the broader
induction/Jacquet/classification framework.
