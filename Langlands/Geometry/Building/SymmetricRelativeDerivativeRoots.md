# Symmetric full derivative pairings and relative roots

This internal supporting unit derives a conditional full-relative-root criterion
from the existing rational derivative pairing and its transport to the actual
relative-root span. It transcribes no new original-literature result.

`RootPairing.isReduced_of_pairing_symmetric` applies to a finite root pairing
over a characteristic-zero integral domain, with torsion-free root module.
For two dependent roots Mathlib's Coxeter-weight criterion gives pairing
product 4. Symmetry makes this a square, hence the pairing is 2 or −2. The
existing two-pairing criteria then identify the roots as equal or opposite.
Thus the full pairing is reduced. Full spanning and crystallographic
integrality are not needed for this helper.

`IsAffineRootSystemWithRankZero.HasSymmetricDerivativePairing` defines symmetry
of real root-coroot evaluation on the full derivative set, including any
multipliable roots.

`hasReducedSimplyLacedRelativeRootSystem_of_derivative_symmetry` assumes a
split torus, a rank-zero-compatible affine root system on the actual reduced
translation space, and equality between its full derivative set and the range
of the actual relative-root forms. It additionally assumes symmetry of the
real root-coroot evaluation for every pair of derivative roots. The existing
transport gives a crystallographic rational root system with the evaluation
pairing and root image exactly the rationalizations of all actual relative
roots. The scalar comparison transfers symmetry, and the helper proves
reducedness, supplying exactly `HasReducedSimplyLacedRelativeRootSystem`.
Empty root systems are allowed, and the affine torsor universe is independent
of the field universe. There is no restriction on the characteristic of the
original field.

Full derivative symmetry is an explicit premise. The theorem does not derive
it from the simple chamber matrix, assert it for an actual group apartment,
prove group splitting, or establish the host affine-diagram theorem.
