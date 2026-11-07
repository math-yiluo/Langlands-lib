# The integral augmentation module for a cocycle splitting module

This internal construction uses the lifted integers
`NormalizedTwoCocycle.CoefficientScalars`, at the full carrier universe.
For a finite group `G`, `regular G` is the module of integral functions on `G`
with right translation, and `ideal G` is the kernel of coordinate summation.
`idealSequence_shortExact` proves the exact sequence from the augmentation
ideal through the regular module to the trivial integral module.

The regular module is explicitly isomorphic to the Library's coinduced
trivial integral module. Consequently, `regular_tate_isZero` reuses the
proved vanishing of its actual Tate cohomology in every integer degree.

These are derived auxiliary constructions for the splitting-module proof of
transfer reciprocity. The coordinate convention is chosen to agree with
the Library's right-translation coinduction. No transfer-reciprocity theorem
or cup-product comparison is asserted by this file.
