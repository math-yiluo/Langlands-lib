# Polynomial comparison of real pair denominators

`RealPositionPairPolynomialStatement` compares the reciprocal pair \(L\)-factor
of two real block lists with that of their position expansions. For each pair
of discrete block data \(A,B\), there is a list of shifts \(b\). If the
corresponding exponents are \(u,v\), each shift contributes a factor
\((s+u+v+b)/(2\pi)\). The product over all shifts and pairs of blocks multiplies
the block denominator to give the expanded denominator. The identity holds at
every complex \(s\), including the zeros of either denominator.

The proof uses the recurrences for the reciprocals of \(\Gamma_{\mathbb R}\)
and \(\Gamma_{\mathbb C}\). At the argument zero the reciprocal vanishes. At
other arguments the recurrence follows by taking the inverse of the Gamma
recurrence and cancelling the nonzero linear factor. Iterating it contributes
the linear factors recorded by `shiftProduct`.

For an induced block paired with a real character, the two position factors
have Gamma arguments shifted by the position exponents and their parities.
One uses the upper exponent with one of the two parities in the duplication
formula. The other argument reaches the complementary upper shift by
nonnegative even steps. For two induced blocks, expanding the first produces
two complex Gamma factors. Their arguments use the sum and a signed
difference of the absolute weights. The block factors use the sum and the
absolute difference. The complex Gamma recurrence moves the signed
difference up by a nonnegative integer. Pair symmetry then permits expansion
of the second list, and multiplication over the finite lists proves the
statement.

This is the polynomial comparison used in H. Jacquet, *Archimedean
Rankin–Selberg Integrals* (2009), Proposition 11.1, author p. 82, with the
block calculations of Lemmas 16.1 and 16.3, author pp. 112–115. The Lean
formula uses the Library's explicit position characters and reciprocal
Gamma factors. The source is `jacquet-2009-archimedean-rankin-selberg`,
SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
