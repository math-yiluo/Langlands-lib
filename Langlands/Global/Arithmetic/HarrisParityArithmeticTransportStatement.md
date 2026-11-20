# Arithmetic transport for the Proposition 4.8 parity correction

`Langlands.Global.Harris.NormTwistInfinityStatement` and
`Langlands.Global.Harris.CMNormConjugationStatement` are derived inputs
for correcting the inducing character in the proof of Proposition 4.8.
They use the actual idele-class norm defining `HeckeCharacter.normComp`.

## Infinity type and relative regularity

The first statement concerns an extension of totally complex number
fields `E' / E`. If `ξ` and `ν` become algebraic after the twists with
exponents `a / 2` and `b / 2`, respectively, the product of `ξ` with the
norm pullback of `ν` becomes algebraic after the twist with exponent
`(a + b) / 2`. Independently, if `ξ` is relatively regular over `E`, the
product is also relatively regular over `E`.

For the infinity equation, use the coordinate product defining
`infiniteAdeleNorm`. At each lower complex place the local norm from
each upper completion is the inverse of the completion map, since
the completed extension has degree one. In complex coordinates it
preserves the modulus. Where the chosen embedding of the upper place
restricts to the conjugate of the chosen lower embedding, interchange
the two exponents in that factor. Thus the norm pullback of the
infinity type at an embedding `σ` has exponent given by the original
type at `σ ∘ algebraMap E E'`. Multiplying the local moduli over the
fibres of the place map yields the modulus product on `E'`.
`Harris.toCharacter_add` combines the two integral types.

For relative regularity, compare the two components over one lower
place on the lower completion, as in `Harris.IsRelativelyRegular`.
`ideleClassNorm_ofCompletion` and the degree-one local norm give
the same factor `ν_τ(x)` for each component at the test point `x`.
Multiplication by this unit preserves the original inequality.
`HarrisDatumArchimedean` contains the complex-coordinate comparisons
for the two choices of embedding.

## Conjugation of the norm

The second statement concerns CM number fields. Their arithmetic
conjugations commute with the field embedding
(`HarrisDatumCharacterRealizationProof` supplies
`Harris.complexConj_algebraMap`). Conjugation sends each completion
tower to the conjugate tower. The induced pair of completion
isomorphisms is compatible with the lower-to-upper completion map
by equality on the dense global fields. Apply
`Algebra.norm_eq_of_equiv_equiv` to each local norm and reindex the
products of places above the lower place. Pass the resulting identity
on ideles to the quotient by principal ideles. This gives the
conjugation law for the actual norm on `IdeleClassGroup`.

Consequently a conjugate-inverse base character has conjugate-inverse
norm pullback. The product with a conjugate-inverse inducing character
has the same property.

## Provenance

Harris defines relative regularity in Definition 2.3 and fixes the
`(n − 1) / 2` algebraic normalization on printed p. 195
(`math_9611226v1.tex`, lines 1180–1219). The proof of Proposition 4.8
uses relative regularity under a norm pullback on pp. 201–203
(lines 1588–1617). The interfaces here concern multiplication by a
base norm pullback and are derived from the completion norm and
character identities above.
[Harris 1998, registered source `harris-1998-local-langlands`](https://arxiv.org/abs/math/9611226)
