# Localized quotients inside affine pullbacks

This internal construction maps the spectrum of a localized quotient into the
pullback of the corresponding closed subscheme. The map is an open immersion:
it is the quotient pullback isomorphism followed by base change of a principal
open immersion. Its second projection is the quotient spectrum map followed
by the localization spectrum map.

A prime of the original source lifts through this map when it avoids the
localizing element and contains the pulled-back ideal. The proof first lifts
the prime through the localization, then uses the quotient range criterion.
An auxiliary scheme lemma transports formal etaleness of the stalk from an
etale open neighborhood, using the isomorphism on stalks of an open immersion.
These are derived constructions from Mathlib and the affine quotient and
scheme etale locus APIs; they assume no good-point or slicing theorem.

For two ring maps `σ, θ : A → B`, the pullback is taken along `θ`, while
etaleness is tested over `Spec A` using `σ`. If the composite ring map
`A → B → B[1/g] → B[1/g]/I B[1/g]` using `σ` is etale, the open immersion
followed by the second pullback projection and `Spec σ` is etale. This follows
by the second projection formula and contravariance of `Spec`.

`exists_formallyEtale_stalk_affinePullback` combines this with prime lifting.
It returns a point above the specified prime where the stalk of the second
projection followed by `Spec σ` is formally etale. The argument cancels the
stalk isomorphism of the open immersion. It does not require finite generation
of `I`, local finite presentation of the ambient composite, or smoothness.
The etale quotient is a hypothesis; selection of equations remains separate.
