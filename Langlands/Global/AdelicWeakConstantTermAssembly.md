# Weak terms from ordinary constant-term automorphy and exponent decompositions

`AdelicWeakConstantTermAssemblyStatement` gives existence of every weak term under ordinary
constant-term automorphy and finite exponent decomposition.
`logSquareIntegrableWeakConstantTermExistence_of_automorphy` deduces existence
of all weak terms from `AdelicStandardConstantTermAutomorphyStatement` and
`AdelicAutomorphicExponentDecompositionStatement`. The full-group weak term
equals the input form, so the input is automorphic on the parabolic quotient
at the top index. Ordinary constant-term automorphy then applies at each
index. Taking the unitary part of its finite decomposition produces the
desired weak term.

`isWeakConstantTerm_of_nested_automorphy` uses the same two premises for
each component of the outer constant term. These give the inner finite
decompositions used in `isWeakConstantTerm_of_nested_decompositions`. The
half-modulus comparison is supplied by `standardNestedHalfModulusCompatibility`.
This yields the equality of the weak terms of the original form and of its intermediate
weak term at the smaller parabolic.

The weak term here follows P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, equation (3.2), PDF p. 10, and Definition 3.7, PDF p. 13.
Lemma 3.8(iii), PDF p. 14, gives the transitivity identity. The registered PDF is
`Delorme--On the spectral theorem of Langlands--2023.pdf`,
SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`,
under `delorme-2023-spectral-theorem-langlands`.
