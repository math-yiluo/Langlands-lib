# Pointwise scaling of finite-exception spectral systems

`SpectralSystem.scale a s` multiplies each eigenvalue in the supplied spectrum
at index `v` by the specified complex unit `a v`. The index type has arbitrary
universe, and the rank is any natural number, including zero. The exceptional
set is unchanged, and the existing symmetric-power construction retains all
multiplicities. No finiteness, continuity or character condition is imposed on
the index-dependent unit.

Scaling by one is the identity; successive scalings multiply their units.
Pointwise reciprocal scaling is the inverse, giving `scaleEquiv`. Scaling
commutes with restriction to any larger finite exceptional set. Its power
trace in degree `k` is multiplied by `(a v)^k`. Its Euler denominator is
obtained by substituting `C (a v) * X`, and its coefficient in degree `i` is
multiplied by `(a v)^i`.

Common pointwise scaling preserves and reflects both `SamePowerTraces` and
`SameEulerPolynomials`, even when the compared systems have different ranks.
The trace comparison retains one finite exceptional set uniform in every
positive power. Reflection cancels the nonzero scalar power pointwise;
reflection of Euler equality applies that cancellation to every coefficient.
Forward transport uses the trace scaling and polynomial substitution formulas.
This does not identify the two comparison relations with each other.

Provenance is internal: the construction applies the published
`Eigenvalues.scale` to each supplied spectrum. The algebraic identities
specialize the published eigenvalue-scaling formulas, and the comparison
identities use filter monotonicity and cancellation over the complex field.
This is numerical infrastructure. It supplies no automorphic realization,
local spectral existence or arithmetic association; applications must provide
the connection to genuine local representations.
