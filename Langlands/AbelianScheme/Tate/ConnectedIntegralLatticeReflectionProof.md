# Integral reflection of rational abelian-scheme isomorphisms

Authors: Worker 1584 and Worker 410.

This proof targets the published proposition
`Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionStatement`.
It is an internal consequence of the existing actual group schemes, Tate
groups, finite étale fibre functor, rationalized category and isogeny descent.
The statement and its imports are unchanged.

The helper `exists_ofHom_eq_of_full_image` treats one rational arrow. Choose a
positive denominator `n` and an actual arrow `f` with `ofHom f = n • r`.
Preservation of the integral image and injectivity of full Tate rationalization
show that the full Tate map of `f` takes every element to an `n`-multiple.
Every full Tate projection to positive level `n` is surjective: multiplication
isogenies give roots on algebraically closed points, and a cofinal factorial
tower supplies a compatible family. Since `n` kills level `n`, the map of `f`
on that level vanishes.

The finite étale torsion premise makes the actual source and target torsion
schemes finite étale covers of the connected locally noetherian base.
Faithfulness of the published geometric fibre functor converts vanishing at the
one supplied geometric point into vanishing on the whole torsion scheme.
Thus `f` kills the actual scheme kernel of multiplication by `n`.
That multiplication is an isogeny under the stated unit hypothesis, so
`IsogenyFactorization.lift` gives an actual arrow `g` with `n • g = f`.
Rationalizing and cancelling the positive integer in the rational Hom module
gives `ofHom g = r`.

Apply this argument to the forward and inverse arrows of the rational
isomorphism. Actual Hom rationalization is injective because positive
multiplication is an isogeny and hence is cancellable on Hom groups.
The rational inverse identities therefore imply the two actual inverse
identities. These arrows form the required actual isomorphism, with both
rational agreements proved.

All Tate groups use every positive index. The proof uses the supplied point
and retains exactly the target's base and finite étale torsion hypotheses.
The characteristic-zero premise is retained, although the proof needs only
algebraic closure and the global unit family. No additional literature theorem
is invoked: this implements the denominator and kernel route described in the
published statement Markdown by composing current Library constructions.
