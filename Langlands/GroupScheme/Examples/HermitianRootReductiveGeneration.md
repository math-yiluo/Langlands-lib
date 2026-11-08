# Rational parabolic radical generation for the actual Hermitian models

Let `k` and `L` be fields in an arbitrary common universe, with `L/k` separable
quadratic. Let `H` be a diagonal Hermitian form on a finite decidable
`Middle : Type`, with specified units realizing its weights. All characteristics
are allowed. For generation assume `H.IsAnisotropic`: zero middle self-pairing
forces the vector to vanish.

The actual weighted Hermitian group scheme is generated on rational points by
the rational images of geometric unipotent radicals of actual parabolic subgroup
schemes. This is the precise equality
`parabolicElementarySubgroup (groupScheme k L H w hw) = ⊤`.
There is no separate reductivity premise: `HermitianRootReductive` proves the
connected reductivity used by the existing dynamic-to-parabolic generation
argument in `HermitianRootModelRadicalGeneration`.

An actual group scheme `A` equipped with an actual group-scheme isomorphism to
this model has the same generation conclusion. The proof first transports
smoothness and affineness through the underlying isomorphism, connectedness
through its homeomorphism, and triviality of the geometric unipotent radical
through the base-changed group isomorphism. It then invokes the existing model
adapter with this proved connected reductivity. Any subgroup of `A(k)` containing
every actual rational parabolic radical image is therefore all of `A(k)`.
Normality of that subgroup is unnecessary.

`rationalPointsEquivParabolicElementarySubgroup` is a multiplicative equivalence
from the actual rational point group to its actual parabolic elementary subgroup.
It uses the proved equality with the top subgroup; its value, coerced to the
rational group, is exactly the original point.

This is an internal consequence of the constructed Hermitian geometry and the
previous explicit matrix generation and dynamic-to-parabolic adapters. It proves
no classification of arbitrary rank-one groups. Finite Weil restriction geometry,
other rank-one cases and unrestricted local Kneser–Tits remain separate obligations.
