# Image equality for the actual adjacent-rank induction

`Langlands.RankinSelberg.adjacentRankModelImage` proves exactly the published
closed proposition `AdjacentRankModelImageStatement.{uF,uV}`. The field and
original complex module have independent universes. Every natural rank,
including zero, is retained. The first block is the specified representation
sigma on its original algebraic module V, with its full standard Whittaker-type
hypothesis and specified nonzero functional ell. The induction is the actual
canonical normalized opposite-parabolic induction with ordered blocks
(r+1,1), on the original tensor carrier with scalar factor `ULift.{uV} C`.
No topology or norm on V, irreducibility, or injectivity of its coefficient
map is assumed.

The motivating statement is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin-Selberg Convolutions* (1983), Section 6.1, printed pp.427–431:
formula (8), compact-orbit sections (10), lower covariance (11), Jacquet
integral (12), double integral (13), and the final spanning paragraph.
The registered source is `jpss-1983-rankin-selberg`, content SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The implemented reverse containment uses invariant cutoff approximation and
admissibility to pass from full-rank compact tests to every Schwartz test.
This closure argument is an internal derivation; it does not identify all
Schwartz tests with compactly supported tests on the full-rank open orbit.

## Uniform analytic input and the common functional

For each arbitrary continuous base quasicharacter chi0, the proof chooses
`AdjacentCompactMatrix.realTwistThreshold F psi sigma hSigma ell chi0`.
Writing N for `coefficientDeterminantOrder` and c for
`characterNormExponent`, this sufficient bound is

```text
C = N - c + (r+1) - r/2.
```

It precedes the real twist u, all vectors, and all test tensors. The imported
`realTwistedCharacter` is literally chi0 multiplied by the target's continuous
unramified character at `LocalFactor.spectralParameter q hq (u : C)`.
`norm_realTwistedCharacter` proves its norm is the canonical normalized
absolute value to power c+u. Thus arbitrary chi0 is included, rather than
replaced by a unitary base character.

The imported `AdjacentRankCompactMatrixConvergence` proves integrability of
square-matrix Schwartz factors times W(h inverse), chi_u(det h), and the
r/2 determinant weight against the actual `generalLinearHaar F.Carrier r`.
Its coefficient growth bound follows from full Whittaker type and is uniform
in W and the test. `AdjacentRankDoubleIntegral.integrable_realTwist` applies
this to a Schwartz fiber norm to prove integrability on the product of the
supplied `rowMeasure nu (r+1)` and that same GL Haar. Its column substitution
uses the exact Jacobian |det h| inverse, and its Bochner Fubini theorem and
`double_integral_eq_modelIntegral` identify the double integral with the
literal model integral on the partial Fourier transformed test. The supplied
self-duality certificate is used for this Fourier equivalence.

`AdjacentRankSectionSurjectivity` proves surjectivity of the normalized-section
map from the compact-test/original-vector tensor product onto the actual
induction. `AdjacentJacquet.integrable_realTwist` in
`AdjacentRankJacquetIntegrability` therefore extends kernel integrability to
every actual induced section and every ambient translate, at this same C.
This supplies the full all-section hypothesis of `AdjacentJacquet.functional`;
no analytic premise is left in the theorem. Its value is the scalar Jacquet
integral at identity, with kernel evaluated on [I,x;0,1] and phase
psi(-x_last). `AdjacentRankJacquetCovariance` proves the standard ambient
Whittaker covariance by an explicit Haar-preserving affine column
substitution. `functional_coefficient` identifies every coefficient of this
one functional with the Jacquet integral at the corresponding group element.

`AdjacentRankJacquetNonzero.functional_ne_zero` constructs a compact local
section whose identity kernel is an indicator times ell(v), with ell(v)
nonzero. The supporting column set is nonempty, open and compact, and the
negative phase is one there. Its positive finite volume for the supplied
product Haar makes the scalar integral nonzero. This proves nonvanishing for
the same functional just constructed, on the original carrier.

## Passing from compact full-rank tests to all Schwartz tests

`modelIntegral_mem_range_of_fixed_approximation` first treats a sequence of
full-rank compact tests Psi_n bounded in norm by one Schwartz test Phi,
eventually equal to Phi at every full-rank matrix, and whose normalized
sections are fixed by one open subgroup J. The imported
`AdjacentDoubleIntegral.tendsto_modelIntegral` from `AdjacentRankJacquetLimit`
proves convergence at each ambient g. Every rectangle sampled by the double
kernel is [h,0] times an invertible upper-column matrix and g, and thus has
full row rank. Eventual equality applies at each sampled matrix, and the norm
of the original integrable double kernel is a dominating function. Dominated
convergence, Fubini and the Fourier comparison give the claimed limit of the
actual model integrals, with all measures and weights unchanged.

The same comparison identifies each approximating model integral with the
coefficient of its normalized section for the identity Jacquet functional L.
`Padic.adjacentRankNormalizedInduced_isAdmissible` applies because full
Whittaker type includes admissibility of sigma. It concerns the exact
original-tensor canonical induction, for every continuous quasicharacter.
`mem_range_fixedCoefficientMap_of_tendsto` then realizes the limiting whole
function by one J-fixed induced vector: coefficients of J-fixed vectors form
a finite-dimensional linear subspace of the scalar function space, which is
closed in its complex product topology. Only this function space is given a
topology; continuity of L and a topology on the original module are unnecessary.

`modelIntegral_tmul_mem_range` supplies the required approximation using
`Padic.adjacentRankInvariantApproximation`. It chooses a compact open J inside
the test stabilizer and the kernel of the outer determinant weight. Its cutoff
tests are J-invariant, norm bounded by Phi, and eventually equal on the
full-rank locus; their normalized sections are all J-fixed. For an arbitrary
Schwartz factor, the proof first applies the inverse of `partialFourierEquiv`.
For an arbitrary coefficient-model vector W, `modelMap_surjective` supplies
an original v mapping to W. Surjectivity here is intrinsic to the definition
of the coefficient image; no injectivity is required.

`range_modelIntegral_subset` extends this pure-tensor membership to every
finite algebraic test tensor by tensor induction. The Jacquet coefficient
map is linear, so its range is a submodule closed under addition.
The opposite inclusion is the imported
`range_realTwistIntegralLinear_coefficients_subset`: section-tensor
surjectivity expresses each actual induced vector as compact-test tensors,
and the exact integral comparison places its entire coefficient function in
the model image. `range_modelIntegral_eq` combines both containments as
sets of functions on the whole ambient GL group.

Finally `adjacentRankModelImage` chooses the uniform C, discharges all-section
integrability for each u>C, selects the constructed functional and its
nonvanishing proof, and rewrites the range equality using
`functional_coefficient`. The statement and its imported pairs are unchanged.
The proof uses no unrestricted gamma/L multiplicativity or later adjacent-rank
factor theorem, and supplies no additional hypotheses to the closed target.
