# Stability under extension of scalars

This internal supporting construction derives scalar-extension stability from
both square stability equalities of an endomorphism over a commutative ring.
The coefficient ring, extension ring and module have independent universes.
No flatness, finite generation or finite dimension is assumed.

The restricted endomorphism on its actual range is bijective: equality of
kernels gives injectivity, and equality of ranges gives surjectivity. Its
inverse, squared and composed with the original range-restricted map, defines
an endomorphism `g` of the original module satisfying `f^2 * g = f` and
`g * f^2 = f`. These identities imply both square stability equalities.
Mathlib's multiplicative base-change map preserves both identities, proving
stability after every extension of scalars. Applying this to `f^b` preserves
exactly the exponent `b`, including its value zero when supplied.

`stablePower_baseChange` states the complex-specialization consequence using
the published `Stable` predicate. This is an algebraic adapter for the
universal-family route to uniform compression stabilization. It does not
prove family finite generation, a specialization bijection, compact fixed
vector base change, or a representation-uniform exponent. No external source
is invoked: the proof follows the two given equalities and Mathlib's tensor
base-change laws directly.
