# The finite family of standard block constant terms of GLₙ

Interior cuts between successive coordinates specify ordered positive block
shapes via the existing `BlockShape.cutEquiv`. The weight for each coordinate
is minus the number of cuts before it. Adding cuts gives the weight comparison
needed for the transitivity of the corresponding normalized constant terms.

The finite family is ordered by the number of cuts, so every strict refinement
appears later. The term associated with the empty cut set is the identity on
functions, under the existing scheme-to-matrix comparison. In this case
the radical consists only of the identity and its quotient has mass one.

On the numerator of an irreducible operator subquotient, quotienting by the
kernel of a block constant term recovers its image with the transported
operator action. These quotient maps have trivial joint kernel by the
empty-cut identity. The realized kernels in this module are submodules over
the monoid algebra of the concrete operators.

These constructions implement the ordering and the whole-group term used in
Langlands's proof of Proposition 2, printed p. 204, final paragraph (Corvallis
Part I, PDF p. 199). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
