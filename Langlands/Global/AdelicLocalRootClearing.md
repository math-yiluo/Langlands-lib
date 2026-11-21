# Root clearing for local uniform-growth meromorphic presentations

`HasLocalCuspidalRootClearing` is the local test condition for an already supplied
uniform-growth presentation of a meromorphic family. One finite set of prescribed
root forms, power, and open neighborhood work for the norm-one Levi cuspidal pairing
of each standard unipotent constant term, against each admissible cusp form and at
each ambient adelic translate. On the presentation's regular domain the extended
test values agree with the root product times the actual pairing.

`hasLocalRootClearing_of_cuspidal_pairings` transfers the same root product to all
point evaluations of the represented family. It uses the exact leading-component
injectivity premise and integrable weighted majorants for the fixed tests. The
regular vectors in the growth space are automorphic and evaluate to the family
on its regular domain.

From meromorphy take a local holomorphic denominator and numerator. Extend the
functions on the open subtype to the coordinate space and shrink to a ball where
the numerator presentation and the test extensions are both valid. The scalar
identity theorem keeps the denominator nonzero somewhere on this ball. Multiply
the meromorphic family and its numerator by the root product, which is entire.
The numerator on the agreement set is a scalar multiple of an automorphic vector.
Linearity of the bundled cuspidal pairings gives the extensions for the multiplied
family. The local pole transfer theorem now supplies the holomorphic point
evaluations. The image of the regular domain is dense in the open presentation,
so the result has the agreement required by `HasLocalRootClearing`.

The proof is derived for Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, §8.6, pp. 225–226. The test-clearing data are a hypothesis,
and the transfer uses the actual pairing of §6.2, (6.8), and the injectivity
of Theorem 6.3. The subsequent coordinate gluing can be done by
`exists_meromorphicInCoordinatesOn_of_local_rootClearing`.
