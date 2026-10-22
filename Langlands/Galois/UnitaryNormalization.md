# Complex unitary Euler-polynomial normalization

Author: Worker 41. The module supplies the polynomial operation used in Harris's weak association.
It makes no assertion that a normalized polynomial family is realized by a
lambda-adic representation.

All names are in `Langlands.GaloisRepresentation`. For a complex number `z`,
`unitaryRoot z` is `z / |z|`. It has norm one when `z` is nonzero; the total
function has value zero at zero. `eulerFromRoots s` is the product
`product (1 - z T)` over the actual multiset `s`, retaining multiplicities.
For a monic complex polynomial `P`, the proved root factorization identifies
`eulerFromRoots P.roots` with `P.reverse`.

`unitaryEigenvaluePolynomial P` is the monic product of the factors
`X - unitaryRoot z` over the roots of the input eigenvalue polynomial.
`unitaryEulerFromEigenvalues P` reverses this monic polynomial.
`unitaryEulerPolynomial P` first reverses its input Euler polynomial and
then applies that construction. Thus its explicit formula is

`product (1 - (beta / |beta|) T)`

over the reciprocal roots `beta` of the original Euler polynomial.
The output has constant coefficient one. When the eigenvalue polynomial has
nonzero constant coefficient, all its normalized roots have norm one.
The intrinsic arguments use the root-multiset factorization, multiplicativity
of reversal, and the formula for the norm of a complex quotient.
The normalized eigenvalue polynomial always has the same degree as its input,
because its root multiset has the same cardinality. If the input has nonzero
constant coefficient, none of the normalized roots is zero; the normalized
eigenvalue polynomial therefore also has nonzero constant coefficient.
The reversal degree formula then proves that the normalized Euler polynomial
preserves the input Euler degree when that input has nonzero constant coefficient.
In particular this applies to the arithmetic Euler polynomials with constant
coefficient one.

Each construction preserves products of nonzero polynomial inputs, by the
root multiset of a product. This allows distinct weights in separate
constituents: no single weight is imposed to perform the normalization.
When every root of a monic eigenvalue polynomial has weight `w`, the operation
equals substitution of `q^(-w/2) T` into its arithmetic Euler polynomial.
The formal substitution uses the inverse of the published `radius q w`;
the identity does not need an even-weight hypothesis or a choice of a
half-integral Galois twist. The multiset proof replaces each root's norm by
that same radius, then distributes the substitution across the Euler factors.

## Source and proof boundaries

Harris (1998), Section 1, printed pp.183-184, defines the compatible-family
Euler polynomial by geometric Frobenius as `det(1 - rho(Frob_v) T)` and
normalizes its reciprocal roots individually by their complex absolute values.
The original passage explicitly allows sums of pure constituents of different
weights and distinguishes this unitary normalization from an arithmetic
Galois representation. Those original pages were read for this construction.
Registered original: `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

The sole project import is the published
`Langlands.Cohomology.Weights.Polynomial`.
Its weight condition and `radius` are reused without alteration.
The continuous-representation and compatible-family modules are not imported.
Mathlib is pinned at `5ed2965256430c3649e86755f9576b54eca72435`
with Lean 4.34.0.

This pair constructs actual complex polynomials. Comparison with an
automorphic local component, the independence of all coefficient realizations,
compatible-family existence, and a realization by a Tate twist are separate
mathematical statements. No such statement is an assumption of a record here.

## Declarations and validation

| Declarations | Role |
| --- | --- |
| `unitaryRoot`, `norm_unitaryRoot`, `unitaryRoot_eq_of_weight` | Actual scalar normalization, norm one for nonzero input, and the fixed-weight formula |
| `eulerFromRoots`, `eulerFromRoots_add`, `reverse_X_sub_C`, `eulerFromRoots_eq_reverse_product`, `eulerFromRoots_eq_reverse` | Euler products and their exact relation with the reversed monic eigenvalue polynomial |
| `unitaryEigenvaluePolynomial`, `unitaryEulerFromEigenvalues`, `unitaryEulerPolynomial` | The three input conventions and constructions |
| `unitaryEigenvaluePolynomial_monic`, `roots_unitaryEigenvaluePolynomial`, `roots_unitaryEigenvaluePolynomial_norm`, `unitaryEigenvaluePolynomial_coeff_zero_ne` | Root multiplicities, monicity, norms and nonzero constant coefficient |
| `unitaryEulerFromEigenvalues_formula`, `unitaryEulerPolynomial_formula`, `unitaryEulerFromEigenvalues_coeff_zero`, `unitaryEulerPolynomial_coeff_zero` | Explicit source product formula and constant coefficient one |
| `unitaryEigenvaluePolynomial_natDegree`, `unitaryEulerFromEigenvalues_natDegree`, `unitaryEulerPolynomial_natDegree` | Degree preservation with the stated nonzero-constant hypotheses where required |
| `unitaryEigenvaluePolynomial_mul`, `unitaryEulerFromEigenvalues_mul`, `unitaryEulerPolynomial_mul` | Product compatibility for nonzero inputs |
| `eulerFromRoots_map_div`, `unitaryEulerFromEigenvalues_eq_weight_substitution` | Substitution under uniform eigenvalue scaling and its pure-weight specialization |

The module compiled natively in the pinned environment with zero diagnostics.
Development compilation and declaration inspection do not establish independent
semantic acceptance or publication.
