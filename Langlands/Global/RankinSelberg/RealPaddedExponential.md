# Exponential lines under real leading-block padding

`RealPaddedProductExponentialStatement` takes a real general linear group
of rank `m` and a finite family of real general linear groups of ranks at
least `m`. The homomorphism that inserts a matrix in the leading block and
pads by identity in each group is continuous. The image under this map of
an exponential is the exponential in the product algebra of the matrix
direction inserted in each leading block and padded by zero.

For one target rank, reindex the two-block diagonal ring homomorphism to
the standard coordinates. Its value on the exponential of a pair of
matrices is the exponential of its value, by continuity and preservation
of sums and powers in the exponential series. For the pair `(X, 0)` the
exponential in the trailing block is identity. This gives the actual
`padGL` convention. Evaluation in any product coordinate commutes with
the exponential by the same series argument. The product continuity is
that of the individual padding homomorphisms in the ambient units charts.

This is the Lie direction calculation for the simultaneous leading-block
embeddings of the compensating subgroup on the two factors. The embeddings
occur in the proof of Lemma 14.1, p. 106 of the author-posted edition.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=106).

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
