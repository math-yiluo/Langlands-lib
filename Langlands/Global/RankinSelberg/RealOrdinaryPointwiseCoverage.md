# Pointwise ordinary normalized generation for real standard models

`realOrdinaryPointwiseCoverage` assumes exact ordinary real continuation.
For every pair of rank-correct irreducible real standard modules, every
nonzero additive scale with its opposite, every compatible quotient measure,
and every complex spectral point, it gives an ordinary test whose entire
normalized value at that point is nonzero. The assertion includes equal and
all unequal ranks.

The proof uses strong induction on the sum of the real ranks. At each step
replace each inducing list by its ordered positive-weight presentation,
which preserves ranks, exact Whittaker models and pair factors. The
singleton cases use the rank-one character integral, the rank-two by
rank-one calculation and the rank-two discrete pair calculation. Ordered
irreducible lists have irreducible sublists, and the dual standard model of
an irreducible list is irreducible.

When the right list is a singleton, the primal step retains the smallest
exponent block on the left. When both lists have several blocks, it removes
the largest exponent block on the right. In either case the leading
comparison applies where the appropriate complementary denominator is
nonzero. At the remaining points the reflected denominator for the smallest
exponent block on the left is nonzero. Use induction on the smaller dual
pair at `1 - s`, apply the leading comparison after permuting the full
dual list, and use normalized reflection to detect an exact ordinary test
of the original pair. Interchanging the lists exchanges the opposite
characters and keeps the larger group first in an unequal-rank integral.

The rank-raising proof uses compatible quotient measures at the intermediate
ranks. The supplied measure is the member of that family at the ordinary
comparison rank. Measures at the other ranks can be chosen by existence of
compatible quotient data.

The exponent alternatives and block reductions implement Proposition 14.3
in §§14.2–14.3, pp. 104–108. [H. Jacquet, *Archimedean Rankin–Selberg
Integrals* (2009), author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=104)

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
