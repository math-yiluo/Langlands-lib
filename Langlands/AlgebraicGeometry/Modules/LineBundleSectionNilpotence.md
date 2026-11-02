# Nilpotence of a line-bundle section with empty generation open

This private draft proves an internal prerequisite of fixed-bundle ampleness
reflection. On a quasi-compact scheme, a global section of an actual line
bundle whose whole generation open is empty has a zero positive tensor power.
There is no reducedness, separatedness or noetherian hypothesis.

The proof uses the published chart constructions from
`Modules.LineBundleSectionClearingProof`. A local frame for the line bundle
induces compatible coordinate maps on all actual tensor powers. On an affine
open inside that chart, the coordinate of the section has empty basic open.
Mathlib's `Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact` makes this
coordinate nilpotent. The formula `LocalChart.E_pow` then makes all sufficiently
large tensor power sections zero on that affine open. Quasi-compactness supplies
a finite subcover; a common positive exponent works everywhere. The sheaf's
uniqueness of gluing gives the global equality to zero.

This is derived content proved from those published constructions and Mathlib's
quasi-compact basic-open nilpotence theorem. It is not a proof of ampleness
reflection. No source statement or comparison is assumed as a certificate.
