# Real diagonals and injective restriction of actual Cartan invariants

This internal construction works for a field `K : Type u` and every natural
rank `n`, including zero. The polynomial separation and final compact-invariant
injectivity results additionally use `[NumberField K]`. The spaces, compact
group and conjugations are the actual ones in `ArchimedeanCartanSymmetricAlgebra`;
no conjugacy or invariant-theory hypothesis is added.

## Real-point separation

`liePolynomial_ext_real` and `cartanPolynomial_ext_real` say that the complex
polynomial tensors on the full complex Lie space and complementary complex
space are determined by their values on `1 tensor X` for actual real vectors
`X`. Their common private proof chooses a finite real basis, complexifies it,
and uses its dual basis to present the symmetric algebra as multivariate
polynomials. Every tuple of real complex coordinates is realized by the finite
sum of those real basis vectors. `MvPolynomial.funext_set` applies because the
image of the real numbers in the complex numbers is infinite. This also
handles a zero-dimensional space, where the polynomials are constants.

## Actual diagonal vectors and compact conjugacy

`RealCartanDiagonal K n` is the product of the real-valued diagonal coordinate
functions at the real and complex infinite places. At a complex place the
diagonal entries are still real. `cartanDiagonalInclusion` sends these
coordinates to the diagonal mixed matrix, with the complex entries obtained
by the usual real-to-complex inclusion, and regards that matrix as an element
of the actual self-adjoint Cartan complement. The membership and linearity
proofs are entrywise. Equality on diagonal entries proves injectivity.

`ComplexCartanDiagonal` and `cartanDiagonalComplexInclusion` are the complex
scalar extensions of these real objects. Flatness of the complex numbers over
the real numbers gives injectivity of the scalar-extended inclusion. These
spaces retain every infinite place, rather than selecting a single factor.

`cartanRealConjugation_diagonal` proves that every actual real complementary
vector `X` has the form `Ad(k)(cartanDiagonalInclusion t)`, with `k` in the
entire `standardInfiniteCompact K n` and `t` in `RealCartanDiagonal K n`.
The proof extracts a real symmetric or complex Hermitian matrix at each
place. It applies Mathlib's `Matrix.IsHermitian.spectral_theorem`, takes its
real eigenvalues for `t`, and assembles the eigenvector orthogonal and unitary
matrices as `ArchimedeanCompactFactors`. The existing
`ArchimedeanCompactFactors.toInfiniteAdelicGL` produces the actual compact
element `k`. Matrix projection ring homomorphisms commute with the products
in actual conjugation, so the component spectral identities give the claimed
identity in the original Cartan complement. The convention is `Ad(k)X =
k X k^{-1}`. No connected-component restriction is used. The matrix spectral
theorem also allows the empty index type, so no positive-rank condition enters.

## Polynomial restriction and injectivity

`CartanDiagonalPolynomialAlgebra` is the complex symmetric algebra of the
complex linear dual of `ComplexCartanDiagonal`.
`cartanDiagonalPolynomialEvaluation` evaluates a dual generator at a diagonal
vector and extends this to a complex algebra homomorphism.
`cartanDiagonalPolynomialRestriction` lifts the dual of the actual complex
diagonal inclusion. Its generator formula and evaluation identity show that
it is restriction of polynomial functions to that subspace.

`cartanDiagonalPolynomialRestriction_injective_on_invariants` proves
injectivity on polynomials fixed by every actual compact element. For a real
Cartan vector, the conjugacy theorem provides a real diagonal and a compact
element. The polynomial action's inverse-adjoint evaluation law, applied to
the inverse of that compact element, identifies its value with the diagonal
value. Equal diagonal restrictions therefore give equal values on every real
Cartan vector. Real-point separation proves equality of the polynomials.

`cartanCompactInvariantDiagonalRestriction` composes the inclusion of the
published `cartanSymmetricCompactInvariants`, the actual trace-duality algebra
equivalence, and this diagonal polynomial restriction. Trace equivariance
transfers compact invariance, so
`cartanCompactInvariantDiagonalRestriction_injective` proves that this
complex algebra homomorphism is injective.

The construction is derived from the actual matrix definitions, the existing
trace/polynomial comparison, symmetric-algebra universal properties, and the
pinned Mathlib spectral theorem and polynomial extensionality; it asserts no
new result from external literature. It supplies the diagonal detection step
toward the invariant-finiteness argument. It does not prove finite generation,
integrality over characteristic coefficients, surjectivity of invariant
restriction, PBW, enveloping central generation, or automorphic differential
growth.

The local real finite-dimensionality instance is explicitly named for this
module, so separate prerequisite branches can be imported together without
colliding generated declaration names. Its type and proof are unchanged.
