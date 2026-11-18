# Unipotence from a schematically dense subgroup of unipotent points

`Langlands.GroupScheme.generalLinearDenseUnipotentSubgroup` proves
`Langlands.GroupScheme.GeneralLinearDenseUnipotentSubgroupStatement.{u}`.
The source is J. S. Milne, *Algebraic Groups* (2017), Corollary 14.11,
printed p. 283, registered as `milne-2017-algebraic-groups` with SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The correspondence with Milne's hypotheses is given in the
[statement's companion Markdown](DenseUnipotentSubgroupStatement.md).

The argument uses the common fixed-vector step of Milne 14.1 on printed
pp. 279–280. Over the algebraic closure, a nonzero finite-dimensional
representation has a simple group-algebra submodule. The Library theorem
`SandwichDimensionBound.action_surjective` supplies Burnside's theorem,
so the group algebra acts surjectively on the endomorphism algebra of that
submodule. Write `R(g)` for the action matrix of `g` on the submodule.
Every `R(g)` has the trace of the identity, since `R(g) - 1` is nilpotent.
The product `R(h) R(g)` is also the action matrix of a group element, so
`tr(R(h) R(g)) = tr(R(h))`. Linearity and surjectivity give
`tr(A R(g)) = tr(A)` for every matrix `A`. The matrix trace pairing implies
that `R(g) = 1`. This gives a nonzero fixed vector over the algebraic
closure. Applying a base-field linear functional that is nonzero on one
of its entries gives a nonzero fixed vector over the original field.

For the group scheme, the proof applies this argument to each nonzero
finite-dimensional representation. The closed embedding into `GL_n` makes
the group scheme affine. The Library's `CentralIntersection` translation
lemmas transfer unipotence from the closed embedding to each representation.
Right translation acts locally unipotently on the entries of the universal
matrix of the embedding and its inverse, using unipotence of a point and
its inverse in the dense subgroup. These entries generate the global
functions over the scalars, which translation fixes. The translation
formula for an arbitrary representation then gives nilpotence of the
difference between the point's action matrix and the identity.

For each coordinate of the fixed-vector equation at the universal point,
its difference from the desired value vanishes on the dense subgroup. The
spectrum of the quotient of the global functions by the principal ideal
of that difference is a closed subscheme through which those points
factor. Schematic density makes the closed immersion an isomorphism,
so the quotient map is injective and the difference is zero. The universal
fixed-vector criterion then gives fixedness on all test schemes, proving
`IsUnipotent G`.
