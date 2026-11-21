# An integral cyclic norm lift for spherical conjugates

Let `E/F` be an unramified cyclic extension of p-adic fields with generator `σ`.
The Lean hypotheses are `IsCyclicAlgebra σ l` and equality of the canonical
absolute ramification indices in the compatible p-adic tower. Suppose the
base change of an invertible matrix has a conjugate in the extension spherical
subgroup. The theorem produces one lift whose cyclic norm is the base-changed
matrix and whose conjugate is spherical whenever the corresponding conjugate
of its norm is spherical.

The characteristic polynomial of the base matrix has integral coefficients.
The polynomial of the integral conjugate has integral coefficients upstairs,
and the field embedding reflects integrality. The constant coefficient is
a unit because it is the determinant up to sign and the relative integer map
reflects units.

Adjoin a root of the resulting monic polynomial over the extension integers.
The separating scalar for the cyclic integer action and the compact cyclic
product theorem give a unit whose cyclic product is the adjoined root.
The map `adjoinRootEval` evaluates the adjoined root of a polynomial `f` at an
element `m` of a possibly noncommutative algebra, provided `aeval m f = 0`.
It uses the central scalar map on coefficients. For matrices, Cayley–Hamilton
supplies the annihilation equation. Evaluation intertwines the coefficient
action and the entrywise field action since the matrix being evaluated is
defined over the base. The image of the unit therefore has the prescribed
ordered matrix norm.

For every spherical conjugate of the matrix, evaluation at the corresponding
integral matrix takes the same unit into the integral matrix algebra. Its
value in the field matrix algebra is the conjugate of the first evaluation.
This follows by comparing the two maps on the coefficients and adjoined root.
Consequently the lift is integral in every conjugate where its norm is integral.
The construction is derived for the unit fundamental lemma in Task 7810.
