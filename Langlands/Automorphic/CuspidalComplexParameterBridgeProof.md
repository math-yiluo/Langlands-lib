# The totally complex cuspidal infinitesimal-character bridge

`Langlands.Automorphic.cuspidalComplexParameterBridgeTC` proves
`Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement` at its
arbitrary field universe. It uses
`Langlands.Global.cuspidalArchimedeanParameterExistenceTC` for the parameter
existence conjunct.

For each list of the required length, the two candidate highest weights are
the two normalized exponent vectors in the given order, with \(\rho\)
subtracted. The highest-weight construction gives a character of the actual
global enveloping center for those weights. Any two matching weights have
the same shifted orbit in each embedding block. The single-block character
comparison gives equality of their restrictions to every block center.
These restrictions determine the global character because their images
generate the entire center. The real indices are empty over a totally
complex field.

The local standard-module calculation shows that each embedding block acts
by its prescribed scalar. The place embedding transfers the calculation to
a nonzero vector of the cuspidal realization. The block center action
commutes with the full operator algebra, and irreducibility extends the
scalar equality to the entire realization. The action map and the scalar
map then agree on the entire center by generation.

If a matching character is regular algebraic, restrict its dominant
integral highest-weight character to each embedding block and compare
with the character of the matching weight. The equality of the shifted
orbits gives exponent lists in \((n-1)/2+\mathbb Z\) with no repeated
entries. Conversely, for Clozel-regular lists, sort each list of integer
parts in decreasing order and subtract \(\rho\) from the corresponding
exponents. The integer parts decrease by at least one between adjacent
positions, which makes each resulting integral weight antitone. Combine
these weights over the places and compare their character with the given
matching character to conclude regular algebraicity.

The normalization follows the published `ComplexPlaceParameterWeights`
and `RegularAlgebraic` modules. The `false` coordinate is the \(z\)-side,
the `true` coordinate is the conjugate side, and the permutations are
independent. The literature reference is Clozel (1990), *Motifs et formes
automorphes*, Definition 1.8 and its remark (printed pp. 89–90), Definition
3.12 (p. 111), and the proof of Theorem 3.13 (pp. 112–113), registered as
`clozel-milne-automorphic-forms-shimura-varieties-l-functions-i-1990`.
