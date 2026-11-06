# The full kernel of commuting subgroup multiplication

Authors: Worker 1783 and Worker 1616.

This internal construction starts from the published actual multiplication
homomorphism for two maps `j : H → G` and `i : K → G` whose images commute on
all test schemes. It works over every scheme base.

If `j` is monomorphic on relative schemes, a point `(h,k)` killed by
multiplication has `j(h) = i(k)⁻¹`. The commuting-image hypothesis makes
`j(h)` commute with every image of `H`; cancellation through `j` makes `h`
central in `H`. The first coordinate is central after every restriction of
the test scheme. The same argument proves second-coordinate centrality when
`i` is monomorphic. Coordinatewise equality in the actual cartesian product
then proves centrality of the full scheme-theoretic kernel. No smoothness,
reducedness, normality or field hypothesis is used.

`commutingMultiplicationKernelLeftCenterMap` is the actual homomorphism from
that kernel into a supplied representative `z : Z → H` of the full centre
of `H`. It factors the kernel inclusion followed by the first projection
using the published represented-subgroup factorization. The companion
composition theorem records this factorization exactly.

The provenance is internal: the proof uses the existing all-test centre,
actual kernel point equivalence, commuting multiplication and represented
subgroup interfaces. This module alone supplies neither a complement nor
finiteness or surjectivity of multiplication.
