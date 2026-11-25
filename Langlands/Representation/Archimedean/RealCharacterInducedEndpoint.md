# Odd endpoint character-induced swap

This module constructs an exact bijective intertwiner from the actual standard module
`[character c, induced d]` to `[induced d, character c]` at the integral endpoint
`b - c.exponent = -|d.weight|`, where `b = d.exponent - |d.weight|/2`,
`|d.weight| > 0`, and `(|d.weight| + c.parity.val) % 2 = 1`.
It proves no claim for the other endpoint parity or outside this endpoint.

The internal argument extends the tail-first construction extracted in
`RealCharacterInducedInterlaced`, using an endpoint parameter observation.
The first factor is the tail multiplier with threshold `|d.weight|`; the second is
the generic multiplier at parameter zero. At zero all generic numerator and
denominator factors are nonzero because the parity is zero or one and the other
indices are nonnegative. The published unrestricted generic recurrence theorem
therefore supplies exact intertwining. The proved integral landing theorem ensures
the composite lies in the character-first standard module.

For injectivity, the induced block already kills modes `|j| < |d.weight|` along the
first axis. The remaining modes `|j| = |d.weight|` have the wrong parity, so they
also vanish. This is `induced_first_low_modes`: the true lower mode threshold is
`|d.weight|+1`. A function in the composite kernel has modes on the second axis
strictly below `|d.weight|` by the tail multiplier. The proved two-axis uncertainty
theorem with thresholds `|d.weight|+1` and `|d.weight|` then kills the function.
The proved compact degree-layer comparison upgrades injection to surjection.
Inverting this reverse-direction bijection supplies the claimed forward map.

`endpointEquiv` chooses that map as a complex-linear equivalence;
`endpointEquiv_isIntertwiner` proves compact and Lie equivariance;
`injective_endpoint` packages the injective intertwiner existence predicate.
The construction adds no landing, uncertainty, exponent-order or classification
hypothesis. Provenance is internal and derived; no external theorem is assumed.
