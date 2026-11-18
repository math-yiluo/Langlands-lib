# Characteristic-zero reductivity and semisimple representations

The theorem
`Langlands.GroupScheme.charZeroReductiveSemisimpleRepresentation.{u}` proves
the unchanged
`Langlands.GroupScheme.CharZeroReductiveSemisimpleRepresentationStatement.{u}`.
For every field of characteristic zero and every connected affine group scheme
locally of finite type over it, connected reductivity is equivalent both to
semisimplicity of every finite matrix representation and to existence of a
faithful semisimple finite matrix representation. There are no additional
hypotheses, and the theorem is universe polymorphic.

Semisimplicity is the statement's sum of nonzero simple stable subspaces,
definitionally the predicate `MatrixRepresentation.IsSemisimple`. Stability
is tested over every commutative ground-field algebra. Faithfulness is the
closed immersion condition `IsClosedSubgroup`.

## Proof

For the forward implication, `characteristicZeroReductiveInvariantIntegral`
provides a normalized invariant integral on the original coordinate algebra.
The theorem `MatrixRepresentation.isSemisimple_of_invariantIntegral` then
proves semisimplicity of each finite representation: averaging gives stable
complements, and the stable-complement criterion gives the required sum of
simple stable subspaces.

The theorem `affineLinearEmbeddingStatement` provides a faithful finite matrix
representation. Applying the forward implication to this representation proves
existence of a faithful semisimple one. It also turns semisimplicity of every
finite representation into existence of such a representation.

Conversely, suppose a faithful semisimple finite representation is given.
Cartier's theorem `affineCartierSmooth` makes the group smooth.
The second conjunct of `semisimpleRepresentationUnipotent` gives
`HasTrivialUnipotentRadical` over the original field. Together with affineness
and connectedness, this is pseudo-reductivity. A characteristic-zero field is
perfect, so `perfectFieldPseudoReductive` gives connected reductivity. Combining
these implications proves both equivalences, including dimension zero whenever
it occurs.

## Provenance

This is a composition of Library theorems and the invariant-integral
semisimplicity helper. Its target is James S. Milne, *Algebraic Groups* (2017),
Theorem 22.42, printed pp.477–478 (PDF pp.493–494), registered as
`milne-2017-algebraic-groups`. The forward proof uses invariant integration
over the original field; it does not implement Milne's reduction to an
algebraic closure followed by the centre and derived-group decomposition.
The converse composes the Library forms of Cartier's theorem, Proposition
19.17, and Proposition 19.11(a). No source definition or statement is changed.
The registered author errata for the 2017 edition and the 2022 reprint were
consulted; the 2022 correction to the eigenspaces in Milne's forward proof does
not affect the invariant-integral argument used here.
