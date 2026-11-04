# Root valuations on the torus points of an actual Levi center

This internal construction is derived from the published normalizer action,
the supplied root-length law and actual standard-Levi Weyl identification.
It introduces no external literature assertion.

`leviCentralTorusPoints i ν I` is a subgroup of the rational points of the
specified torus. It is the inverse image, under the actual torus-point map,
of the image of the full abstract center of the literal standard Levi
`levi i ν I` in the ambient rational-point group. Its membership lemma
expresses exactly an actual central Levi element mapping to that torus
point. It neither substitutes the scheme center nor asserts equality with
the points of a central split torus.

The three general normalizer lemmas require a monomorphic torus map.
Commutation of the ambient point with the inverse of a particular
normalizer representative fixes that point under the inverse normalizing
automorphism. Evaluating characters therefore gives invariance under the
representative's actual character action. When this representative is an
actual reflection in a relative root and the torus is split, that root is
sent to its negative. Its point value equals its inverse, hence has square
one. Ambient affineness is used in the reflection result; no connected
reductivity or local-field topology is assumed.

For a selected simple root `α ∈ I`, the supplied
`actualLeviWeylIdentification` puts the corresponding Coxeter generator in
the image of the actual Levi Weyl quotient. The representative membership
description supplies a literal normalizer point belonging to the Levi.
The supplied `RootLengthComparison`, splitness,
`HasRelativeRootSystem i` and genericity of `ν` identify its scheme Weyl
class with the actual reflection in `α`. A torus point in
`leviCentralTorusPoints i ν I` commutes with the inverse representative,
because its ambient image comes from the full abstract Levi center.
The preceding evaluation argument gives
`simpleRootPointValue i ν α t ^ 2 = 1`. For any `ValuativeRel k`, valuation
multiplicativity and the order then give valuation one.

Finally, for `I = Finset.univ.erase α`, all simple roots other than `α`
have valuation one at such a point. Thus the existing
`IsNoncentralNegativeTorusPoint i ν t` predicate is equivalent to the
single strict inequality that the omitted root value has valuation below
one. The forward proof locates the strict root witness at `α`; the reverse
proof uses valuation one on every other simple root. The finite
simple-root type and its decidable equality are retained. If the
simple-root type is empty there is no omitted-root parameter, and no
existence is asserted.

All fields have arbitrary universe `u`. The two point-normalizer and
point-centralizer comparisons remain explicit. This unit proves no
strict complex-character bound, exponent sign trichotomy, proper-index
Jacquet vanishing, analytic sufficiency or self-association theorem.
