# Cancellation and division of the four-crossing family

This module derives cancellation and simple-pole division for the
explicit `RealInducedSwapRegularizedFamily` from the existing finite-support
cancellation, Fourier uniqueness, and finite-layer division theorems.
It makes no appeal to an analytic-continuation axiom or an external source.

`totalOrder c` counts the removed denominators. `Cancels d e c` is an explicit
sufficient condition: a finite `AC` multiplier has cutoff at most the first
induction weight, a finite `BD` multiplier has cutoff at most the second
weight, or a finite final `AD` multiplier has cutoff at most the larger weight.
With valid choices, each alternative makes the actual regularized `rawMap 0`
zero. The proof identifies the center with the recurrent composite and applies
the corresponding existing cancellation theorem. In the final-factor case,
the zero target-valued recurrent map has zero underlying function and hence
zero ambient map.

Fourier uniqueness shows that scaling a multiplier on its actual parity
class scales its Frobenius map. Multiplying the four scalar relations gives
`fullMap z = z ^ totalOrder c` times the generic shifted full map whenever
`z` is nonzero and all four shifted parameters are generic. Restriction gives
the same identity for `rawMap`. When `totalOrder c = 1`, the defined
`normalizedMap z` therefore equals the generic shifted raw map at those
parameters.

Residue cancellation makes the quotient weakly analytic at zero for every
fixed input. This is analyticity after every algebraic complex linear
functional. The quotient also preserves each compact degree bound, including
at zero by the finite-layer derivative theorem. Each fixed input's entire
quotient family consequently has a finite-dimensional range.

The cancellation and simple-order assumptions remain explicit. This file
does not extract them from unlinkedness, construct the target-valued limiting
equivalence, establish limiting Lie intertwining, or prove
`RealInducedSwapStatement`.
