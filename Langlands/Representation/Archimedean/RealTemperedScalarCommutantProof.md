# Scalar algebraic commutant for tied real standard modules

`Langlands.Archimedean.realTemperedScalarCommutant` proves the unchanged
`Langlands.Archimedean.RealTemperedScalarCommutantStatement` from
[`RealTemperedCommutantReduction`](RealTemperedCommutantReduction.md).
For every `n : ℕ` and `ds : List RealBlock` with `realRank ds = n` and
pairwise equal real parts of the block exponents, every complex-linear
endomorphism of the actual `O(n)`-finite functions in `realStandardModule n ds`
that commutes with `realStandardRep n ds` and every `realStandardLie n ds`
operator is multiplication by a complex scalar. No continuity or boundedness
of the endomorphism is assumed.

## Implemented proof

This is an internal composition of Library results.
[`realTemperedScalarCommutant_of_cases`](RealTiedScalarCommutantCases.md) splits
on whether `ds` contains a discrete-series block, meaning an induction block
of nonzero weight.

- With no such block, `realTiedNondiscreteReduction`
  ([`RealTiedScalarAssembly`](RealTiedScalarAssembly.md)) expands weight-zero
  blocks into characters and uses the character-list reduction to spherical
  cyclicity. The proof supplies `RealSphericalCyclicProof.realSphericalCyclic`
  ([`RealSphericalCyclicProof`](RealSphericalCyclicProof.md)) for that input.
  This branch includes the empty list, whose rank is zero.
- With a discrete-series block, `realTiedDiscreteScalarCommutant_of_cases`
  ([`RealTiedDiscreteScalarCommutantCases`](RealTiedDiscreteScalarCommutantCases.md))
  splits on `IsRealDiscreteExponentSeparated ds`: every block sharing the
  complex exponent of a discrete-series block must be an induction block of
  the same absolute weight. The proof supplies
  [`realTiedDiscreteSeparatedScalarCommutant`](RealDiscreteSeparatedProof.md)
  for separation and
  [`realTiedDiscreteCoincidentScalarCommutant`](RealDiscreteCoincidentProof.md)
  for its negation.

Both splits preserve the original rank and common real-part conditions; no
condition on imaginary parts or on the shapes of blocks is added to the
conclusion. Each branch proves the same scalar-commutant predicate for the
actual module. The composition uses neither the Langlands quotient theorem
nor tied Langlands classification or the tied tempered irreducibility target.
