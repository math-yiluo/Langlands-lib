# Relative normal-idempotent rigidity for almost-simple fibres

Worker 632, with the relative interface and route proposed by Worker 47,
Worker 5254's projection-injectivity theorem and induced-algebra interface,
and Worker 96's field-ascent root-normal-closure argument.

`relativeAlmostSimpleNormalIdempotent` proves the exact
`RelativeAlmostSimpleNormalIdempotentStatement` in every universe. Every
original coefficient algebra under `T` and its specified structure map is
retained, including nonreduced and zero rings.

The original transformation reconstructs an actual idempotent of `G_T`.
Its affine-test conjugation equation extends to all scheme tests through
the affine presentation of `G_T × G_T`. Almost-simple geometric fibres
persist under the arbitrary base change. The closed fixed-image retract
is smooth with geometrically connected fibres. The unit-étale loci of its
inclusion and of its unit inclusion give exact identity and triviality on
opens. The field dichotomy covers the base, and nontrivial fibres make the
two opens disjoint. Their clopen decomposition gives a ring idempotent.

The identity-carrier natural comparison of original coefficient algebras
with induced presentations recovers the exact original transformation.
Its value after quotienting by `1 - X(e)` is the original point, and after
quotienting by `X(e)` it is the identity point. Naturality proves these
formulas for every original algebra and point.

For uniqueness, the quotient formulas identify the transformation with the
factor projection at the candidate idempotent, using the existing
`IdempotentPoints.eq_proj_iff`. Worker 5254's
`IdempotentProjection.eq_of_proj_eq` distinguishes different idempotents
by a prime and a nontrivial affine point of the corresponding field
pullback. Almost-simple geometric fibres supply that nontriviality.

The proof does not infer equality on a nonreduced base from equality on
geometric fibres. Smooth monomorphism geometry supplies the actual open
equalities; the fibre argument determines which opens occur.
