# Ordered products of actual additive-subgroup actions

Let `k` be a field, `n` a finite matrix index type, `G` a group scheme over
`k`, `rho : G -> GL(n)` an actual group-scheme representation, and
`x_i : Ga -> G` a finite ordered family of group-scheme homomorphisms.
The images of the `x_i` need not commute, and the homomorphisms need not
be embeddings.

For univariate polynomial matrices `P_i(T)`, `polynomialMatrix` constructs
`P_0(T_0) ... P_(d-1)(T_(d-1))` with independent formal parameters.
The construction uses `MvPolynomial.finSuccEquiv` recursively, putting the
first matrix on the left. `coefficientProduct` is the correspondingly
ordered product of the univariate coefficient matrices.
`polynomialMatrix_coeff` proves that the multivariate coefficient at an
exponent vector `a` is exactly `coefficientProduct P a`.
`polynomialMatrix_aeval` proves that evaluation in every commutative
`k`-algebra gives the product of the evaluated matrices in that same
order. There is also a base-field evaluation corollary. An empty family
gives the identity matrix and its constant coefficient.

`orderedPoint x S t` is the product, in index order, of the actual points
`x_i(t_i)` over an arbitrary commutative test algebra `S`.
`actionPolynomial rho x` uses the actual universal univariate matrix of
each restricted representation `rho.restrict (x_i)`.
`actionPolynomial_aeval` identifies its entrywise evaluation with
`rho.affineMatrix S (orderedPoint x S t)`. This holds for every commutative
test algebra, including algebras with nilpotents; no rational-point
identity is substituted for this comparison.

The finite operator polynomial `orderedCoefficients` is obtained by
applying `Matrix.toLin'` to these multivariate coefficients.
`evaluation_orderedCoefficients` identifies its base-field values with the
original `rho.affineAction` at the ordered product, called
`orderedOperator`. The coefficient formula becomes
`orderedCoefficients_eq_prod`: the coefficient at `a` is the ordered
product of `AdditiveDividedPowers.dividedPower (rho.restrict (x_i)) (a i)`.
As endomorphisms multiply by composition, the rightmost factor acts first
on column vectors. No factors are interchanged.

Over an infinite field, the existing polynomial coefficient-span theorem
then gives three consequences: the actual ordered operators and the
ordered divided-power products have equal linear spans; they preserve
exactly the same subspaces; and their images of any fixed vector have
equal linear spans. These conclusions concern the ordered product family
and do not assert that every point of `G` belongs to that family.

The proof of the coefficient formula inducts on the number of parameters,
using the coefficient compatibility of `finSuccEquiv`, matrix
multiplication, and the coefficient of a univariate polynomial times a
constant. The evaluation compatibility follows by extensionality of
algebra homomorphisms on variables and then induction on the ordered
matrix product. The actual-action comparison uses the published
all-algebra univariate evaluation theorem, restriction along the supplied
homomorphisms, and the original representation's multiplication law.
The final span and invariant-subspace results reuse
`Langlands.LinearAlgebra.PolynomialCoefficients` and its compatibility with
linear maps and application to a fixed vector.

This is a derived algebraic unit, with no external source assertion.
It constructs and compares the polynomial of a supplied ordered family
of actual actions. It does not supply root subgroups, ordered root
coordinates, Steinberg highest vectors or support bounds, entire induced
space equality, or irreducibility. In particular it does not identify
noncommuting root-group actions with independent coordinate translations
and does not prove `SteinbergBigCellStatement`.
