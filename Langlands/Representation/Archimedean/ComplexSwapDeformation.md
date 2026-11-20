# Affine deformation of an adjacent complex swap

For an adjacent pair `d, e` in a complex standard module of rank `n`, shift the
exponent of `d` by the same complex parameter `z` in both orders. The position
of `d` moves by one under the swap. The exponent-shift equivalence identifies
each deformed space with its space at zero as a representation of `U(n)` and
transports the Lie action to an affine family on that fixed space.

`swapParameters d e` consists of the shifts for which the two exponents have
different imaginary parts. Taking imaginary parts in the first integer
equality of `IsComplexLinked` proves that the shifted pair is unlinked there.
This set is infinite since it contains all nonnegative integer translates of
one point whose imaginary part differs from the excluded value by one.

For each such shift, the Library's unlinked swap theorem gives a bijective
intertwiner between the deformed standard modules in the two orders.
`exists_affine_swap` conjugates this intertwiner by the exponent-shift
equivalences to the fixed spaces. It intertwines their original compact
operators and their deformed Lie operators along real matrix directions.

This is an internal construction for the reordered-product constituent
comparison of Badulescu and Renard (2010), Remark 2.3 (p. 1123, PDF p. 10) and
Proposition 2.4 (p. 1124, PDF p. 11). For the linkage relation and the
rank-two comparison, see Tadić (2009), `tadic-2009-gl-n-c-gl-n-r-unitary-duals`,
§3 (author's PDF p. 11) and §1 (pp. 5–6), including (1-1) and the sentence
after (1-2). The implemented swap uses `complexStandardUnlinkedSwapReduction`
applied to `complexGLTwoUnlinkedIrreducible`.
