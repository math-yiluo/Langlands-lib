# Successive represented positive-weight kernels

This internal derived construction extends `RootWeightQuotient` with the
successive subgroup inclusions and exact all-test kernels. It reuses the
represented-subgroup point equivalences, `homOfPoints`, and the existing kernel
range characterization. The supplied data are the same regular root-height
chart and independent natural-weight commutator bound, allowing zero weights.

Term `d` has cutoff `d + 1`; its successor has cutoff `d + 2`. Antitonicity of
the generated levels gives `subgroupStep`. The represented point equivalences
transport this inclusion to `stepPoints`. Composing with the existing inclusion
into the ambient chart proves its naturality by cancellation of a monomorphism.
Yoneda then constructs the actual group-scheme map `step`. Its composite with
the term inclusion is the successor inclusion. This also identifies its range
on every scheme test with the ambient successor subgroup. Closedness follows
by cancellation through the ambient closed immersion, and normality follows
from the normality of the successor in the ambient group.

The exact-weight quotient kills a term point precisely when its original
coordinates of weight `d + 1` vanish. The point already has zero coordinates
below this weight. These two facts are exactly the coordinate condition for
membership in the successor, which requires vanishing below `d + 2`.
`range_kernelι_quotientMap` therefore identifies the actual scheme-theoretic
kernel range with the successor inclusion on all scheme tests. Combining this
identity with the flat, surjective and locally finitely presented projection
from `RootWeightQuotient` gives the represented fppf quotient predicate
`isFppfQuotient_quotientMap`.

This supplies exact successive quotients for the supplied positive subgroup
construction. A finite series and the construction and descent for every
supplied relative radical remain separate obligations. No additional external
source translation is claimed.
