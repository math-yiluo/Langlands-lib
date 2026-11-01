# Common convergence on actual coefficient models

Author: Worker 468. The module adapts the published tail-product and Iwasawa
proofs in `WhittakerTorusMellin` and `WhittakerMatrixConvergence`, and reuses
the published compact-averaging APIs in `WhittakerModelInclusion`.

For a p-adic field `F` with canonical topological data, a representation
`sigma` of `GL_(n+1)(F)` on an independent-universe complex carrier, a
nontrivial unitary additive character `psi`, and full
`IsOfWhittakerType n (standardCharacter psi n) sigma`, the real number
`modelMatrixConvergenceBound F hU psi sigma hsigma` is a common bound for
all actual coefficient models. Its explicit premise `hU` is the closed
`UniformFiniteFunctionMellinConvergenceStatement`.

`modelMatrixConvergenceBound_spec` states that whenever `Re(s)` exceeds
this bound, the shifted full-matrix integral with exponent `s + n/2`
converges for every equivariant functional `ell`, every full-matrix
Schwartz--Bruhat test `Phi`, and every function in the actual bi-smooth
matrix-coefficient span of `glModelRepresentation psi n sigma ell`.
The bound is chosen before all these inputs. `glModel_matrixConvergesOnRight`
packages the same specification into the existing
`GodementJacquet.MatrixConvergesOnRight` predicate for each model.

The model carrier is the actual image subtype
`(glCoefficientModel psi n sigma ell).toSubmodule`. No model equivalence or
irreducibility assumption is used. All natural `n`, including zero, and all
functionals, including zero, are covered. The original full Whittaker-type
predicate retains admissibility, finite generation over the group algebra,
and the one-dimensionality of the whole equivariant-functional space.
The measure is exactly `generalLinearHaar F.Carrier n`, with the canonical
normalized absolute value and the existing shift `jpssShift n`. Units,
the general linear group, and the upper unipotent group carry the Borel
measurable structures used by the imported integration theorems.
A local instance gives the image subtype its canonical additive group;
it does not change the carrier or its action.

## Implemented proof

`uniform_torusMellin` pulls an entire finite torus family back through the
tail-product automorphism. The uniform Mellin premise at positive weights
`i + 1` supplies a single threshold before every additive test. For any
Schwartz functions `phi` on `F^n` and `J` on `F^(n+1)`, its test is
`initTail F phi J`. The formula `torusIntegrand_tailProd` identifies the
pulled-back integrand; `measurePreserving_tailProd` and its measurable
embedding transfer integrability to diagonal coordinates. Finiteness of
each pulled-back function follows from `IsFiniteFunction.comp` and
continuity of the automorphism. No threshold is selected after `phi` or
`J` has been supplied.

`lintegral_torus_lt_top_of_uniform_terms` adapts the finite-sum norm estimate
of `lintegral_torus_lt_top` in `WhittakerMatrixConvergence`. Its fixed
exponents are `sliceExponents F n`, independent of the test and right
translate. `exists_uniform_slice_bound` bounds the unipotent integral by
a real constant times this fixed monomial and a Schwartz box test. The
unipotent equivariance formula separates the Whittaker value from that
integral. Expanding this value and using the triangle inequality bounds the
torus integral by a finite sum of integrals of the absolute values of
`torusIntegrand F (phi chi) J (chi * torusWeight F (sliceExponents F n)) s`.
Integrability of those terms, supplied as an explicit fixed-parameter
hypothesis, makes this bound finite.

`exists_common_matrix_halfPlane` applies `uniform_torusMellin` to the image
of a fixed family `X` under multiplication by this fixed `torusWeight`.
Both factors are continuous translation-finite functions, so each product
is too. This supplies a threshold before the Whittaker-like function,
all its expansion coefficients, every right translate and every matrix
test. At any parameter in that half-plane the preceding norm estimate
holds at every `k` in the integral subgroup. The published finite-coset
sum and Iwasawa integration formulas then prove finiteness of the full
matrix integral. The cosets depend on the function and test, but their
terms already converge at the same threshold; no later maximum of
thresholds is taken. The integral subgroup has Haar mass one, and each
coset subgroup has finite mass. Continuity supplies measurability of the
matrix integrand.

`exists_common_glModel_halfPlane` uses the finite family in
`CoefficientTorusExpansion`, which precedes every functional and model
vector. For a right translate `k`, apply that expansion to
`glModelRepresentation psi n sigma ell k w`; evaluation at a diagonal
matrix is evaluation of `w` at `diag(a) * k`. Admissibility and this
expansion give `glModelFunction_isWhittakerLike`. The preceding theorem
therefore supplies the unshifted bound for all model functions. Subtract
`Re(jpssShift n)` once to obtain the shifted bound. This shift is made
before any functional, test or vector is supplied.

`modelCoefficient_converges_of_modelFunctions` transfers integrability at
a fixed parameter to an individual smooth coefficient. The published
`exists_compactOpen_matrixTest_invariant` chooses a compact open subgroup
fixing the test on the left and having determinant absolute value one.
Admissibility passes to the actual image model.
`exists_eq_sum_modelPointAverage` then expresses a smooth functional as a
finite sum of compact averages of point evaluations over a smaller
subgroup. `matrixIntegral_sum_modelPointAverage` supplies integrability of
the resulting coefficient from integrability of the model functions with
conjugated tests and translated vectors. A bound uniform over tests and
vectors applies to all of these terms at the same parameter.

`exists_common_modelMatrix_halfPlane` extends this integrability from
individual smooth coefficients to their entire complex span using
`matrixConverges_of_mem_span`. The threshold stays fixed before the
functional and every member of this span.

`exists_modelMatrixConvergenceBound` supplies the fixed expansion using
`modelAsymptoticTransfer` with the published closed theorem
`Langlands.whittakerTypeAsymptotic`. Thus the expansion interface is
discharged by an actual proof. Classical choice defines
`modelMatrixConvergenceBound`, and its choice specification proves
`modelMatrixConvergenceBound_spec` and the existing convergence predicate.

## Provenance and remaining scope

This is internal derived support. It strengthens the quantifier order of
the published per-function, per-test convergence route by reusing fixed
slice exponents and assuming the explicitly stronger uniform Mellin
convergence assertion. The published `WhittakerMatrixConvergence` theorem
alone does not justify exchanging those quantifiers. Its Iwasawa and
finite-sum estimates are adapted here with that distinction preserved.
`UniformWhittakerSliceBound` fixes the exponents but supplies no Mellin
convergence. The published asymptotic theorem and
`ModelAsymptoticTransfer` discharge the coefficient expansion; neither
supplies the uniform Mellin premise. No literal new assertion from the
original literature is claimed.

The module does not prove `UniformFiniteFunctionMellinConvergenceStatement`.
That premise remains required in the selected real bound and every final
convergence assertion. This unit supplies no rational continuation,
normalized generator, transformed-coefficient assertion or functional
equation, and proves neither of the host task's closed two-block gamma
or L propositions. No two-block multiplicativity result is used.
