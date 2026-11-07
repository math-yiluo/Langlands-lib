# The norm from coinvariants to invariants

For a representation `A` of a finite group `G` over a commutative ring `R`,
all at universe `u`, `coinvariantNorm A` is the actual norm
`a ↦ ∑ g, g · a`, descended to the coinvariant quotient and with codomain
the invariant submodule. Its value on a quotient representative is
`normToInvariants A a`.

This internal construction uses the norm's invariance under precomposing
with any group element to descend it via
`Representation.Coinvariants.lift`. Tate cohomology in degree minus one is
the homology of the coefficient short complex with arrows the ordinary
group-homology differential `d₁₀` and the norm. Its vanishing therefore
implies that every norm-zero vector lies in the image of `d₁₀`, which is
exactly the submodule killed in the coinvariant quotient. Applying this to
the difference of two representatives proves injectivity.

Vanishing in degree zero makes every invariant vector's `zeroClass`
vanish. The established norm-quotient presentation of degree-zero Tate
cohomology then gives an actual vector with that norm, proving
surjectivity. `coinvariantNorm_bijective` combines the two arguments, and
`coinvariantNormEquiv` packages the same map as a linear equivalence.

The provenance is internal. The proof uses the Library's existing
`minusOneShortComplexIso` and `zeroClass_eq_zero_iff`, and Mathlib's
`range_d₁₀_eq_coinvariantsKer`. It assumes precisely the displayed
vanishings in degrees minus one and zero. It asserts no transfer
comparison or unconditional vanishing.
