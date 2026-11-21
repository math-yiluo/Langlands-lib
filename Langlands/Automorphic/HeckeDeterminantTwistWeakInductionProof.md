# Direct Euler weak induction of a determinant-twisted presentation

`Langlands.Automorphic.heckeDeterminantTwistWeakInduction` proves the published
[`HeckeDeterminantTwistWeakInductionStatement`](HeckeDeterminantTwistWeakInductionStatement.md)
at its two universes: the fields share a universe, and the presentation carrier
has its own. The proof uses the actual presentation `P.heckeDeterminantTwist ν`
and keeps the rank identity from the original weak induction of `ξ`.

Intersect the cofinite source comparison with the complement of a finite
ramification set for `ν`, supplied by `exists_finset_isUnramifiedAt`. At a place
`v` in this intersection outside the twisted presentation's exceptional set,
`v` is also outside the original exceptional set, so the source comparison
applies. Above `v` the ramification indices remain one. Each component of
`ξ * HeckeCharacter.normComp ν` is trivial on integral units: both the component
of `ξ` and, by `normComp_isUnramifiedAt`, the norm-pullback component are trivial
there.

Let `a = ν.finiteUniformizerValue v`, the value at the canonical lower
uniformizer. The published lemma
[`Langlands.Global.FiniteAdelicGL.completion_uniformizer_value`](../Global/FiniteAdelicGL/SphericalArithmeticTransport.md)
identifies the canonical normalized discrete valuation with the completion
valuation and evaluates that uniformizer at `exp (-1)`. Given **any** upper
uniformizer family `ϖ`, the published
[`normComp_finiteComponent_uniformizer`](../Global/HeckeCharacterUnramifiedNorm.md)
then gives the value `a ^ f(w | v)` at `ϖ w`. This norm lemma uses ramification
index one to compare with the image of the lower uniformizer, discards the
integral-unit ratio, and takes the norm of the lower uniformizer to the local
degree, which is the residue degree here.

The [actual twisted presentation's Euler polynomial](HeckeTwist/CuspidalSpectralTwist.md)
is the original polynomial composed with `C (a : ℂ) * X`. Rewrite the original
polynomial by the weak-induction comparison for `ϖ` and distribute the
composition over the product using `Polynomial.prod_comp`. In the factor at
`w`, the substitution multiplies the coefficient of `X ^ f(w | v)` by
`a ^ f(w | v)`, exactly the multiplier in the inducing character's component.
Thus each factor agrees, and so does the full product for every uniformizer
family.
