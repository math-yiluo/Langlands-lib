# Irreducibility of full represented intersection pieces

This internal unit concerns the actual represented geometric-lemma intersection
objects and functors. It proves `FullIntersectionPieceIrreducibleStatement`:
if both intersection parabolic morphisms are isomorphisms, an irreducible
representation of the source Levi has an irreducible geometric piece.
The field universe and coefficient-carrier universe are independent, and the
actual induced piece has carrier universe `max u v`.

The geometric helpers assume an actual isomorphism between the outer source
and target Levis. If the source intersection is full, its own Levi is full by
the published reductive-group result. The intersection conjugation isomorphism
then identifies the target intersection Levi with the outer target Levi.
Composing its actual closed embedding into that Levi with this identification
gives a closed self-embedding of a connected reductive group. The published
closed-self-embedding theorem makes it an isomorphism. The target intersection
parabolic and its Levi inclusion are consequently isomorphisms. The supplied
outer-Levi isomorphism need not be the ambient conjugation: only its existence
is used. A full source by itself is not asserted to imply a full target.

`fullLeviJacquetRepresentationEquiv` bundles the existing actual full-Levi
Jacquet linear equivalence and its proved action comparison into an equivariant
linear equivalence. Its target is the original representation pulled back along
the actual composite Levi inclusion. When the parabolic and Levi inclusions
are both isomorphisms, that map on rational points is surjective. Pullback of an
irreducible action along this surjection is irreducible, and transport across
the equivalence proves `leviJacquet_isIrreducible_of_isIso`.

For the piece theorem the full source parabolic has full Levi, so the preceding
Jacquet result applies. Pullback along the actual conjugation equivalence `D.e`
preserves irreducibility by surjectivity. Induction along the full target
parabolic preserves irreducibility by the actual full-parabolic induction
result. This is exactly the three-functor composition defining `pieceFunctor`.
The outer-Levi-isomorphism corollary supplies the full target from the geometric
helpers and applies the same proof.

The topological hypotheses for these actual functors are the existing ones:
a Hausdorff topological field, affine ambient group scheme, and locally compact
nonarchimedean rational points with their canonical topology. No supercuspidal,
admissibility or finite-length premise is used. The geometry helpers require
only the represented intersection datum and an isomorphism of its outer Levis.
This unit constructs no intersection data or geometric filtration, proves no
Weyl count or detection theorem, and does not prove the host unitarizable
constituent statement. All assertions are derived from the implemented actual
functors and published algebraic constructions; no new external source theorem
is assumed.
