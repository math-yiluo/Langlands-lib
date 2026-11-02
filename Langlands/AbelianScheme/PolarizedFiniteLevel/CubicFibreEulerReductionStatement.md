# Finite cohomology and the Euler-square reduction for the cubic bundle

`CubicFibreEulerReductionStatement` is an internal reduction for the existing
`CubicFibreCohomologyStatement`. It uses every published prerequisite and the
actual datum `a : Datum P (Spec K) g d n`, with the same canonical tensor cube.
It applies over every field and for every natural `g`, `d`, and `n`.

The first conclusion is unconditional: the actual cubic bundle has finite
cohomology in the sense of `HasFiniteCohomology`. Thus every actual derived
cohomology module is finite dimensional over `K`, and all sufficiently high
cohomology objects vanish.

The second conclusion is a conditional reduction. For any finite-cohomology
witness, vanishing of every positive-degree cohomology object and the equality
`chi(a.cubicBundle)^2 = 6^(2*g) * d^2` imply that the actual degree-zero
cohomology has dimension `6^g*d`. The Euler-square equality is in `ℤ`.

## Provenance

This internal statement packages two elementary consequences needed in the
assigned cubic-fibre proof. Its unconditional finiteness assertion specializes
the published `smoothProperLineBundleEulerPolynomial` to the datum's canonical
bundle and the tensor power `3`. Its conditional assertion follows from the
published `eulerCharacteristicBasic` identity for positive-degree vanishing and
the uniqueness of a nonnegative square root in `ℤ`.

This module states the reduction. It does not prove higher-cohomology vanishing,
ampleness, or the required geometric Euler-square equality, and therefore does
not by itself prove `CubicFibreCohomologyStatement`.
