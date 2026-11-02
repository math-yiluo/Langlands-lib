# Polynomial points with simple integer equations

This internal construction supplies the polynomial point-choice step of the
good-point existence argument for smooth equivalence relations. Worker 303
designed that argument and specified the prime-choice interface; Worker 101
implemented the construction and proofs below. No good-point existence or
scheme slicing theorem is assumed or proved by this module.

For any commutative ring `A`, index type `ι`, prime `Q` of `MvPolynomial ι A`,
and polynomial `h` outside `Q`, `SimpleIntegerRootPrimeData Q h` packages:

- a prime `a` avoiding `h`;
- the equality of contractions `a.comap C = Q.comap C` in `A`;
- for each coordinate `X i`, an integer polynomial `P` whose value lies in
  `a` and whose derivative value lies outside `a`.

The definition `simpleIntegerRootPrime` chooses such data by classical choice
from the proved `exists_prime_simpleIntegerRoots`. The universe levels of `A`
and `ι` are independent and arbitrary. The index type need not be finite.

The proof first defines `simpleIntegerRootSet K` as the elements of a
commutative ring `K` satisfying an integer polynomial with nonzero derivative.
The theorem `infinite_simpleIntegerRootSet` proves that this set is infinite
when `K` is an algebraically closed field. Given any finite candidate set,
choose an integer `n` larger than its cardinality and nonzero in `K`; at least
one of two consecutive integers works. The polynomial `X^n - 1` is separable
and has exactly `n` distinct roots. Each is a simple root of the corresponding
integer polynomial, contradicting the proposed cardinality bound. This proof
works uniformly in every characteristic.

For the prime-choice theorem, put `p = Q.comap C` and let `L` be the algebraic
closure of its residue field. The coefficient map `A → L` has kernel `p`.
The image `H` of `h` in `MvPolynomial ι L` is nonzero: otherwise all its
coefficients would be in `p`, placing `h` in `map C p`, hence in `Q`.
The multivariable polynomial identity theorem on products of infinite sets
then gives a tuple `α : ι → L` of simple integer roots where `H` is nonzero.
This identity theorem applies to arbitrary index types because each polynomial
uses only finitely many variables.

Take `a` to be the kernel of evaluation at `α`. It is prime since its target
is a field, avoids `h`, and contracts to `p` since evaluation preserves
constants. Evaluation also commutes with evaluation of integer polynomials,
so each simple integer equation for `α i` supplies the required equation and
nonvanishing derivative at `X i`. All mathematical inputs are proved Mathlib
results or the preceding lemmas in this module.
