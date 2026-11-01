# Actual orbit measures across source cuts

This internal specialization transports a supplied compatible set of actual
orbit measures across an inclusion of source cuts. The permutation must be
increasing on the original source blocks, exactly as required for equality of
the actual radical stabilizer intersections.

`parabolicOrbitNestedIntersectionCutEquiv` restricts the existing actual kernel
cut equivalence to those intersections. Its value theorem records the original
kernel coordinate; no representative is reselected.

`parabolicOrbitIntegralMeasures_cutMap` pushes the supplied kernel Haar measure,
intersection Haar measure and quotient measure along the actual kernel,
intersection and quotient equivalences. The pushforwards retain regularity,
both Haar invariances and finiteness on compact sets. The generic simultaneous
transport theorem proves the full compatibility property, including averaging
integrability and the Weil integral formula. The three projection theorems
specify these measures literally as pushforwards, without rescaling.

This module applies to every commutative topological ring with its canonical
Borel structures, conditional on the supplied measure data. It makes no
cross-cut representation comparison or homological claim.
