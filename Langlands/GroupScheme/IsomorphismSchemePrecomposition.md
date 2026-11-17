# Source precomposition of supplied Isom representatives

This internal construction is derived from the published natural all-test
`LocalGroupIso` interface, constant families from actual group isomorphisms,
and the classification property of `GroupIsomorphismScheme`.

An actual isomorphism `i : G' ≅ G` precomposes each natural local family from
`G` to `H`. Its value at every parameter point and group point is the original
family applied after `i`. Naturality follows from composition and the original
family's naturality. Precomposition by the inverse gives the inverse operation,
and the construction commutes with every refinement of the parameter.

`GroupIsomorphismScheme.precompose` retains the actual parameter scheme and
precomposes its universal family. The required classification bijection on
every relative test is the old classification bijection followed by the
precomposition bijection.

Suppose an action of `A` on `G` and an action of the same group `A` on `G'`
are intertwined by `i` on every relative test. Then source precomposition
intertwines the canonical inverse-precomposition actions on the two Isom
representatives. The proof evaluates the universal families and uses exactly
the supplied intertwining equation, including its value at the inverse
acting point.

`OuterIsomorphismScheme.precompose` therefore transports a supplied outer
quotient through this compatible change of source. It retains the class
scheme and class morphism, so flatness, surjectivity and quasi-compactness
are inherited. Invariance and the unique same-test acting point are the
original properties after the proved equality of the two actions.

No reducedness, affineness, field, reductivity or finiteness assumption is
used. Both the initial representative and the compatible actions are inputs.
The construction proves no independent representability or quotient-existence
theorem for reductive group schemes.
