# The actual signed rank and component normalization of the split primal atlas

`Harris.primalFramingRank` applies the verified atlas height calculation to
the actual split primal rigidifier. It is a locally constant function on the
reduced base spectrum. The source ranks come from the extended special frame.
Quotient coefficient extension supplies the reduced target's ranks. On each
test chart the pulled-back rank is the height of the evaluated rigidifier.

`primalFramingRank_zero_iff` identifies vanishing of this function with the
actual zero-height condition on all test charts.
`primalDrinfeldFramedAtlasOfRankZero` then constructs the actual Drinfeld
triple from that zero fibre and the supplied square-height certificates.
The local projected prime-height criterion also implies this vanishing.

When the value of the central rank is divisible by the division degree,
`Harris.primalComponentOrder` gives the locally constant first coordinate by
its negative exact quotient. The exact signed multiplication equation is
part of the result. It characterizes the coordinate uniquely and implies
that its zero fibre agrees with the zero fibre of the actual primal rank.
The divisibility input depends on the special division-order geometry.

The construction gives the primal sign and rank normalization in the split
component comparison of Rapoport–Zink, (6.17) and Lemma 6.44, printed
pp. 309–310, and Harris 1997, Appendix, (A.1)–(A.4), printed pp. 113–114.
