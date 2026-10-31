# Actual complementary-block continuations from transformed matrix data

Worker 396. Internal derived prerequisite for the actual rank-one matrix
functional-equation comparison. Field and representation-carrier universes
remain independent; the original representation may be reducible.

`RankOneBlockReduction.BlockZeroReduction` is a Prop-valued assertion about the
actual scalar unequal-rank block integrals when the smaller group is `GL1`.
For every allowed block `(j,k)` and first coefficient-model vector `f`, one
vector `f0` of the same model has the identical scalar integral in block zero,
for every inverse Whittaker second function and every complex parameter.
The additive rectangular measure is always the product from the supplied `nu`.
The quotient measure `mu` is unchanged and arbitrary in this reduction.

`blockZeroReduction` proves that assertion for a full Whittaker-type first
representation and a nonzero specified functional. It inducts on `j`.
At each positive step, the published `unequalRankCompactSupport` supplies a
compact set containing all rectangular coordinates where the specified
coefficient can be nonzero, uniformly in the smaller group variable.
The published `AdjacentBlockReduction.exists_adjacent_integral_coefficient`
then integrates the last row into one vector of the original coefficient
model and gives the exact identity from block `(j+1,k)` to `(j,k+1)`.
The induction composes these identities; at zero rows the numerical block
parameter is forced by the rank equality.

This scalar identity is valid at every parameter and requires no quotient
integrability. Compact rectangular support is used by the imported row
integration theorem to justify its rectangular Fubini calculation. The
result does not claim that absolute convergence of the lower block can
be reversed through a row integral.

`rationalContinuation_of_matrix` assumes in addition a positive first rank,
a compatible rank-one quotient measure, and the actual coefficient-model
matrix analytic assertions. It reduces the specified block to zero rows
and applies the published original block-zero continuation transfer to the
resulting same-model vector. Equality of the totalized scalar integrals
on a right half-plane transfers that continuation, with its denominator
nonvanishing clause, to the original block. No extra original block
rationality or convergence premise is introduced.

`dualBlockZero_rationalContinuation_of_iota` gives the precise genuine dual
continuation needed by positive-rank gamma assembly. It first transfers the
supplied inverse-transpose matrix assertions to the constructed first-dual
coefficient model for `psi.scale(-1)`. Full Whittaker type and nonvanishing
of its functional follow from the published actual first-dual transport.
The preceding arbitrary-block result is applied at complementary block
`(r-0-1,0)` to the actual vector

```text
translatedFirstDualModelEquiv psi sigma ell (blockWeylAt 0 r hrpos) f.
```

The second dual of the actual canonical constant-one second vector is
proved to be the actual canonical constant-one vector for `psi.scale(-1)`.
Unfolding `dualUnequalRankModelIntegralAt` therefore yields exactly the
continuation asserted for its complementary rectangular integral, with the
unsigned long Weyl transform, the actual block Weyl right translate, the
supplied `nu`, the same compatible quotient measure and the same spectral
variable all retained.

The derivation uses published compact support and row integration rather
than a multiplicativity assertion or a conditional I1/I2/I3 comparison.
It imports the separately submitted OriginalBlockZero and DualConvergence
pairs unchanged. It asserts no new original-source transcription. These
results establish continuations of the actual scalar integrals; they do
not prove complementary-block absolute convergence, the paired normalized
functional equation, or the final all-rank gamma comparison.
