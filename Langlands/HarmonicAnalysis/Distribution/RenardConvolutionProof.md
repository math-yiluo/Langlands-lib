# Renard II.3.10: all compact distribution convolution laws

Worker 150, Task 5394. The theorem `RenardConvolution.statements` proves exactly
`Langlands.HarmonicAnalysis.Distribution.RenardConvolution.Statements.{uG}`,
retaining its unrestricted group universe and all nine conjuncts. Source:
Renard, French version of 9 July 2026, II.3.10, printed pp.50–51 /
PDF pp.56–57; registered as
`renard-2026-representations-groupes-reductifs-padiques`.

The final proof assembles the following existing proofs from the four companion
proof modules; their paired Markdown explains each implemented argument.

- `ambientTensor`: the original ambient distribution tensor has compact support
  in the product of supports; extended evaluation agrees with support descent.
- `regularity`: all four scalar kernels are locally constant, compact inputs
  preserve compact tests, and the test and smooth formulas agree pointwise.
- `associativity`: three iterated extended evaluations agree by group
  associativity, using the actual published compact convolution operation.
- `mixedAssociativity`: all three identities hold with smooth intermediate
  functions having exactly the four prescribed test-kernel values. Extended
  tensor Fubini justifies the two changes of evaluation order.
- `haarDensity`: left and right invariant measure densities convolve to the
  exact left and right scalar kernels. Product-test Fubini and invariant
  substitutions prove the identities, with the target's weaker right measure
  hypotheses retained.
- `evaluation`: both inversion kernels evaluated at the group identity give the
  original distribution's evaluation on every scalar test.
- `bilinearUnit`: convolution is complex bilinear and the original Dirac
  distribution at the identity is a two-sided unit.
- `diracLaws`: Dirac convolution gives the original left and inverse-parameter
  right distribution actions, and two Dirac distributions multiply at the
  group product.
- `heckeCompatibility`: the actual test density map carries the published Haar
  Hecke convolution to compact distribution convolution.

The ambient-test representative arguments and finite tensor expansion concern
only the existing full algebraic dual. They impose no additional continuity,
countability, unimodularity, normalization or universe assumptions. The final
assembly does not alter the published statement pair or its imports.
