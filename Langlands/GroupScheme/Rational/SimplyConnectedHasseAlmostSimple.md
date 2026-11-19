# Reduction of the simply connected Hasse kernel to almost-simple groups

`NumberFieldAlmostSimpleSimplyConnectedGaloisHasseKernelStatement`
asserts the natural cocycle Hasse kernel for almost-simple, simply
connected groups over number fields. It uses the actual finite Galois
covers and their pullbacks at all places, in the same universe as the
simply connected kernel.

The theorem `numberFieldSimplyConnectedGaloisHasseKernel_of_almostSimple`
reduces the simply connected kernel to this assertion. Decompose a
simply connected group into its finite product of simply connected
almost-simple factors. Mapping a cocycle into each factor preserves
local triviality because coefficient maps commute with pullback.
Apply the arithmetic premise in each factor. The resulting cochains
assemble to a cochain of the product using the actual equivalence
between product points and families of points. The coboundary equation
can be checked by projecting onto each factor. Transport the product
trivialization across the inverse of the given group isomorphism.

This internal construction proves the reduction from the stated
arithmetic premise, including the case of an empty product.
