# Algebraic boundedness of full-lattice stabilizers

This internal argument supplies the boundedness step used in the proof
of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 8.3.1, printed pp. 295–296 / PDF pp. 326–327.
The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
It concerns the actual matrix action and the canonical valuation integer
ring; it needs no topology, discreteness or reductivity.

All three public lemmas are in the
`Langlands.GroupScheme.MatrixRepresentation` namespace and allow a
valued field `K : Type u` in arbitrary universe. The coordinate lemma
only assumes that the integral submodule is finitely generated; it does
not require fullness or a finite coordinate index type. The matrix
lemma uses a finite index type and a full lattice, meaning a finitely
generated integral submodule whose `K`-span is the entire coordinate
space. It bounds every matrix carrying the lattice into itself, without
assuming that the matrix is invertible. The final lemma assumes an
actual closed representation of the original affine group and a subgroup
whose matrices preserve the full lattice. Neither smoothness,
connectedness, Henselianity nor a residue-field condition is required
for any of these helpers.

First, a finite set of field elements has a common nonzero valuative
upper bound, by induction and totality of the valuation relation.
For any fixed bound the corresponding ball is a submodule over the
valuation integer ring. It therefore bounds the entire integral span of
a finite generating set. Applying this observation to a coordinate
projection proves `lattice_coordinate_bound`.

For a full lattice, the scalar extension spans the vector space.
`IsLocalization.mem_span_iff` expresses the standard basis vector in
column `j` as a nonzero fraction times a vector of the original lattice.
If a matrix preserves the lattice, the image of that vector has uniformly
bounded coordinate `i`. Multiplication by the fixed fraction gives the
uniform bound in `matrix_entry_bound_of_preserves_lattice`.

Finally, `isAlgebraicallyBounded_of_preserves_lattice` applies the
published closed-representation theorem
`isAlgebraicallyBounded_of_entries`. The subgroup condition supplies
inverse stability, so the entry bounds also bound the inverse
coordinates and hence all actual regular functions on the original
affine group.

These are elementary internal linear-algebra consequences, rather than
an existence theorem for integral models or stable lattices. The
registered 2024 corrections, source `kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 37 adds a perfect-residue hypothesis to Section 8.3; none of its
residue-field or reductivity hypotheses is used in this elementary
boundedness argument.
