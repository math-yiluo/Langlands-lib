# Inversion of a left-invariant probability measure

The module proves `probabilityInvariantInversion` of type
`ProbabilityInvariantInversionStatement`. For a measurable group with measurable
multiplication and inversion, any left-invariant probability measure is
invariant under inversion.

For a nonnegative measurable `f`, apply Tonelli's theorem to `f(x⁻¹ y)`.
Integrating first in `y` gives the integral of `f` by left invariance. Integrating
first in `x` and changing `x` by left multiplication by `y` gives the integral
of `x ↦ f(x⁻¹)`. The outer integrals preserve each constant because the mass is
one. Applying the equality to indicators of measurable sets gives equality of
the measures.
