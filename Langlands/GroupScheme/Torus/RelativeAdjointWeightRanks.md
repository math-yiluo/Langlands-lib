# Locally constant ranks of actual relative adjoint weights

For a smooth affine group scheme over `Spec R` and an actual homomorphism
from a split torus with finite coordinate index `I`, every actual
integral-exponent adjoint weight space is finite projective over the
arbitrary commutative base ring `R`. Its rank at a prime is locally
constant. Moreover, a single open neighbourhood of any prime makes all
of these ranks constant at once.

The projections constructed in `RelativeAdjointWeights` retract the
actual weight-space inclusions. Finite projectivity of the ambient
actual Lie module from `Lie.SmoothFiniteProjective` therefore gives
finite projectivity of each weight submodule.

For simultaneous constancy, the proof first shows that only finitely
many weight summands can be nonzero over the whole ring. Mathlib's
`LinearMap.finsuppLinearMap_bijective_of_moduleFinite` writes the actual
universal adjoint coefficient map as a finitely supported family of
endomorphisms. Outside that support the coefficient endomorphism is
zero, while it is the identity on its own weight space. The
corresponding weight space must consequently be zero.

`exponentWeightRank` uses Mathlib's `Module.rankAtStalk` of these
actual submodules. Finite projective modules are flat and finitely
presented, so `Module.isLocallyConstant_rankAtStalk` applies. Intersecting
the finitely many open equal-rank fibres for the nonzero summands gives
`exists_open_exponentWeightRanks_eq`. Every other summand has rank zero
everywhere. Thus `exponentWeightRankProfile`, which records all integral
exponent ranks, is locally constant.

The provenance is internal: these are consequences of the actual
coefficient-retraction construction, actual smooth Lie finite
projectivity, and Mathlib's finite-module and local-rank results.
There is no noetherian, reduced, connected-base or chosen-basis
assumption. These are ranks of the actual relative weight summands;
comparison with the character-weight dimensions of actual geometric
fibres and the reductive-locus openness theorem remain separate
obligations.
