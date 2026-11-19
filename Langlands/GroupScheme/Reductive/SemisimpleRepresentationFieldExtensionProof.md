# Simple and semisimple representations under extension of the base field

`Langlands.GroupScheme.semisimpleRepresentationFieldExtension` proves
`Langlands.GroupScheme.SemisimpleRepresentationFieldExtensionStatement.{u}`
for every universe `u`. The proof applies
`semisimpleRepresentationFieldExtension_of_algebra` to
`Langlands.Algebra.semisimpleScalarExtension.{u,u,u}`.

For (a), scalar extension preserves stable subspaces and reflects membership of
vectors from the original coordinate space. This gives irreducibility descent.
For semisimplicity descent, a stable complement after extension gives a
projection commuting with the scalar extensions of the original operators.
Applying a ground-field linear functional on the extension field that sends one
to one gives a projection onto the original stable subspace whose kernel is a
stable complement.

For (b), irreducibility makes the original representation a simple module
over its coefficient operator algebra. The scalar-intertwiner hypothesis
identifies its commuting endomorphisms with the scalars. Jacobson density on
a finite basis then gives the full matrix algebra. Acting by the extended
elementary matrices on a vector with a nonzero coordinate gives nonzero scalar
multiples of each standard basis vector. Thus any nonzero stable subspace
contains the whole basis, giving irreducibility after extension.

For (c), the original representation is a faithful semisimple module over
its finite-dimensional operator algebra, so that algebra is semisimple.
The bicommutant comparison identifies its centre with the centre of the
self-intertwiner algebra and transfers the étale-centre hypothesis.
The algebra theorem gives semisimplicity of the tensor-extended operator
algebra under either the separable-field or the étale-centre hypothesis.
Its image on the extended coordinate space is semisimple by surjectivity.
The invariant subspaces for that image are exactly the stable subspaces of
the extended representation, so every stable subspace has a stable complement.
The operator-module comparison gives the required sum of simple stable
subspaces. See the [representation reduction](SemisimpleFieldExtensionReduction.md)
and the [algebra proof](../../Algebra/SemisimpleScalarExtensionProof.md).

The exact statement formalizes J. S. Milne, *Algebraic Groups* (2017),
Proposition 4.19, printed pp. 90–91 (PDF pp. 106–107), with Remark 4.18
on endomorphisms. The registered source is `milne-2017-algebraic-groups`
(SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
The coordinate and all-affine-test conventions are described in the
[statement](SemisimpleRepresentationFieldExtensionStatement.md).
