# The zero-row branch of rectangular gauge Mellin convergence

This internal helper uses the published normalization of `rectangleMeasure`.
If `r - (t + 1) = 0`, its matrix space has one point and total mass one.
The published `lintegral_rectangular_eq_pad_of_gap_eq_zero` therefore identifies
the inner lower integral with evaluation at the padded point. Applying this
identity at each representative of the smaller Whittaker quotient proves
`rectangular_mellin_eq_padded_of_gap_eq_zero`, with the determinant weight
and the outer quotient measure unchanged.

The identity applies to every extended nonnegative kernel and real exponent;
it needs no measurability or finiteness hypothesis on the kernel.

The theorem `adelicSimpleRootGaugeRectangularMellin_of_gap_eq_zero` then
applies the proved padded-gauge Mellin theorem. For every nonnegative
exponent τ, it chooses a common nonnegative threshold before quantifying
over the gauge Ξ. Its threshold is the padded theorem's
`max(0, τ + 3 + ∑ (j + 1)(t − j))`, where `0 ≤ j ≤ t`, so it is independent
of the individual gauge and its Schwartz–Bruhat function. Rewriting the
rectangular integral by the identity above transfers unconditional
finiteness for every larger σ. All number fields in universe u, proper
blocks, and both published measures are retained. The nonempty rectangular
case remains a separate obligation.
