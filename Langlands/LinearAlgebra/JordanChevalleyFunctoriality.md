# Functorial additive Jordan decomposition

This module defines canonical additive Jordan components for endomorphisms of
finite-dimensional vector spaces over a perfect field. The field and each of
the two vector spaces have independent arbitrary universes. There is no
characteristic restriction, and the zero-dimensional case is included.

The construction is derived from Mathlib's
`Module.End.exists_isNilpotent_isSemisimple` and
`Module.End.isNilpotent_isSemisimple_unique`, together with the existing
semisimplicity descent theorem in
`Langlands.GroupScheme.Lie.RepresentationSubquotient`. No external structural
result about algebraic groups is assumed here.

## Components and their properties

`jordanSemisimplePart f` chooses the semisimple part provided by Mathlib's
Jordan decomposition theorem. `jordanNilpotentPart f` is its complement
`f - jordanSemisimplePart f`. The properties theorem proves that the chosen
semisimple part is a polynomial in `f`, that the complementary part is
nilpotent, that the chosen part is semisimple, and that the two commute.
The uniqueness theorem identifies the chosen part with the semisimple term
of every commuting nilpotent-plus-semisimple decomposition of `f`.

## Common polynomials and naturality

The elementary theorem `aeval_intertwines` says that a linear map intertwining
two endomorphisms intertwines the evaluations of every common polynomial.
`isNilpotent_of_surjective_intertwiner` descends nilpotence along a surjective
linear intertwiner. Neither elementary lemma requires finite dimension or
perfection. `commute_sub_aeval` is the corresponding polynomial commutation
identity.

`exists_common_jordan_polynomial f g` applies Jordan decomposition to the
endomorphism `f.prodMap g` of the direct product. Its semisimple part is a
polynomial in that endomorphism. The coordinate projections intertwine the
original endomorphism and its polynomial with the corresponding operators
on each factor. Their surjectivity descends both nilpotence and
semisimplicity. Thus one polynomial produces the semisimple components of
both `f` and `g`, even when the dimensions differ.

`jordanSemisimplePart_intertwines` uses that common polynomial and uniqueness
to prove that every linear map intertwining `f` and `g` also intertwines their
canonical semisimple components. Subtraction gives
`jordanNilpotentPart_intertwines`. The linear map need be neither injective
nor surjective.

These results concern finite-dimensional linear endomorphisms. They do not
construct Jordan components on infinite-dimensional coordinate algebras,
prove that such components are derivations, or prove Cartan generation.
