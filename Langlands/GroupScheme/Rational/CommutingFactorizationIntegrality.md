# Spectral integrality from a commuting torus and additive factorization

This internal adapter uses the canonical topology on actual rational points,
independent anisotropic torus compactness, additive-point compact powers, and
positive-power integrality descent. It does not construct a group-theoretic
factorization.

`rationalPointsMapContinuousMap` bundles the actual point homomorphism induced
by a morphism of affine group schemes as a continuous map for the canonical
rational-point topologies. It is the existing functoriality theorem with the
original underlying function.

Suppose an affine group scheme locally of finite type over an actual
nonarchimedean local field is anisotropic in the existing split-rank-zero sense.
A closed torus in that group is also anisotropic. Its structure morphism is
affine and locally of finite type because its closed immersion composes with
the ambient structure morphism. Independent torus compactness therefore makes
its whole rational-point space compact. The continuous image of that space in
the ambient group is compact and contains every nonnegative power of each
mapped torus point.

For a positive-power factorization of an ambient point into the image of such
a torus point and the image of the coordinate-one point of a finite vector
group, the additive factor has compact powers by `AdditivePointPowers`.
If the two factors commute, `PointPowerIntegrality` combines the two compact
sets, obtains integrality of the actual representation matrix of the positive
power, and descends integrality to the original matrix. The coefficient helper
then puts every characteristic-polynomial coefficient in the canonical
valuation integer ring, expressed as `coeff ≤ᵥ 1`.

The field universe is arbitrary. Every finite matrix index type, including
the empty type, and every vector-group dimension, including zero, are allowed.
There is no characteristic, perfectness, faithfulness, or representation
semisimplicity premise. The explicit positive-power factorization and
commutation remain hypotheses: this auxiliary unit does not yet prove the
unconditional anisotropic reductive spectral-integrality statement.
