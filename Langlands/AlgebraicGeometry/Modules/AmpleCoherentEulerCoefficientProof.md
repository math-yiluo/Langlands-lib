# Ample coefficients from integral ideal filtrations

The proof begins with the successor-dimensional coefficient criterion
for a nonzero coherent ideal on an integral proper scheme. A strict support
bound at the successor dimension makes the corresponding coefficient vanish.
Otherwise the ideal has full closed support, and the support bounds force the
ambient dimension to equal that successor. The lower-dimensional criterion,
applied to the exact-dimensional ample section cokernel, gives positivity of
the structure-module coefficient through the integral positivity helper.
The ideal quotient has smaller support, so additivity identifies the ideal
coefficient with this positive coefficient.

For a closed immersion, the integral source inherits local Noetherianness,
compactness and separatedness from the ambient scheme. The pulled-back bundle
is ample. Equality of actual closed-support bounds transfers the given support
bound to the ideal. The affine projection formula and pushforward Euler
comparison identify its polynomial with that of its closed pushforward.
Consequently nonnegativity and strict positivity detection transfer as well.

The full integral-ideal filtration premise supplies coherent terms, actual
short exact sequences, and an endpoint isomorphism with the coefficient sheaf.
Finite pushforward preserves coherence of the factors. These data form a
`CoherentFiltration`. Its support-bound equivalence gives a common support
bound on all factors from the bound on the endpoint. Applying the transported
integral-ideal criterion to every factor and telescoping coefficients proves
the successor criterion for the endpoint. Finite sums of nonnegative
coefficients are positive exactly when some factor has a positive coefficient;
the short exact support union identifies this with failure of the smaller
support bound for the endpoint. This also handles a filtration of length zero.

Finally, `ampleCoherentEulerCoefficientReduction` proves
`AmpleCoherentEulerCoefficientReductionStatement` by induction on the natural
dimension bound. The base is the actual finite-support Euler positivity
criterion. The successor step is the filtration argument above, using the
preceding dimension's criterion on the actual section cokernel.

This is an internal derivation. Worker 137 supplied the integral
structure-module positivity helper, which uses Worker 689's coherent ample cut
and Worker 1013's section-cokernel coefficient identity. Worker 1013 also
supplied the actual pushforward comparison and coherent-filtration telescope.
The complete integral-ideal filtration theorem remains an explicit premise.
This reduction does not prove that premise or the final smooth proper
line-bundle Euler polynomial statement.
