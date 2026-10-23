# Unordered nonzero complex eigenvalues

This module constructs the elementary spectral algebra needed for unramified
parameters. Its provenance is internal: it specializes Mathlib's symmetric
powers, multiset sums and products, and diagonal matrix operations to complex
units, and proves the compatibility identities directly. It asserts no
representation-theoretic classification or external source theorem.

## Carrier and operations

`Langlands.Unramified.Eigenvalues n` is exactly `Sym ℂˣ n`, the subtype of
multisets of complex units having cardinality `n`. Its coefficient field and
carrier universe are fixed to those of `ℂ`; both ranks in the module range over
all natural numbers. Rank zero is allowed. The multiset records multiplicities:
equal eigenvalues are not collapsed to a set.

In the namespace `Langlands.Unramified.Eigenvalues`, `ofTuple` sends
`z : Fin n → ℂˣ` to the multiset of its list of values. `ofTuple_reindex` proves
invariance under any permutation of `Fin n`. `ofTuple_surjective` proves every
such multiset has a tuple representative. Its proof inducts on the rank, removes
one multiset entry at each successor step, and uses `Fin.cons` to rebuild the
tuple. No ordering is part of the resulting spectrum.

`directSum s t` is multiset addition, with rank `n + m` for independently chosen
ranks `n` and `m`. `ofTuple_append` identifies it with concatenating tuples.
`power s k` raises each unit to its natural power `k`. The module proves
compatibility with tuples and direct sums, the identity at exponent one, and
`power (power s a) b = power s (a * b)`. These definitions retain multiplicities
even when distinct original eigenvalues acquire equal powers.

## Scalar invariants

For eigenvalues `z₁,…,zₙ`, the definitions are

* `powerTrace s k = ∑ᵢ zᵢ^k`, for every natural `k`;
* `eulerPolynomial s = ∏ᵢ (1 - zᵢ X)`, a polynomial over `ℂ`.

The polynomial is the denominator of the usual Euler factor; this module does
not define an analytic function or its reciprocal. Explicit tuple formulas
are proved by converting mapped multiset folds to finite sums and products.
The zeroth power trace is the complex image of the rank. The trace of exponent
`b` after raising the spectrum to exponent `a` is the original trace of exponent
`a * b`. Direct sums add every power trace and multiply Euler polynomials.
In particular, the interface includes all positive powers, rather than only
the ordinary trace.

The Euler polynomial evaluates to one at zero and is therefore nonzero. Its
natural degree is exactly the rank: nonzero eigenvalues give linear factors of
degree one, and the degree of their product is the sum of these degrees. This
also covers the empty spectrum, whose polynomial is one and whose degree is
zero.

## Actual matrix realization

`diagonal z` is an element of
`Matrix.GeneralLinearGroup (Fin n) ℂ`, the units of the square complex matrix
ring. Its value is the diagonal matrix with entries `z i`; its inverse is the
diagonal matrix of inverse units. Both inverse equations follow from diagonal
matrix multiplication and the complex-unit inverse equations.

`trace_diagonal_pow` proves, for every natural `k`,
that the trace of the `k`th power of this actual matrix equals
`powerTrace (ofTuple z) k`. The proof uses Mathlib's diagonal-power and
diagonal-trace identities.

`charpolyRev_diagonal` proves that its Mathlib `Matrix.charpolyRev` is
`eulerPolynomial (ofTuple z)`. Here `charpolyRev A` is literally
`det (1 - X • A.map Polynomial.C)`. The proof identifies this polynomial matrix
entry by entry with the diagonal matrix having entries `1 - C (z i) * X`, then
applies the diagonal determinant formula.

`exists_matrix` combines tuple surjectivity with that explicit diagonal
construction. Every spectrum is realized by an invertible matrix with the
specified Euler polynomial and all natural power traces simultaneously. This
is a proved existence conclusion, not extra realization data assumed in the
definition.

## Scope

The module is algebraic and equips no carrier with a topology. It does not
identify these multisets with a quotient of all semisimple matrices, prove
uniqueness from traces or Euler polynomials, or assign them to representations.
In particular, normalized principal series, spherical Hecke eigencharacters,
Satake existence and uniqueness, and compatibility with actual automorphic
local components require separate constructions and theorems. The name
`Unramified` records the intended application and imposes no such theorem as an
assumption.
