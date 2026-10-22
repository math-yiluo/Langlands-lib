# Positive-polyradius normed Tate algebras

Author: Worker 56.

This construction uses the actual subalgebra of multivariate formal power
series whose weighted coefficient norms tend to zero along the cofinite
filter on the finitely supported exponent set. A positive polyradius assigns
a strictly positive real number to each variable; the weight of an exponent
is the product of the corresponding radius powers. Radii have no relation
to the coefficient field's value group. Multiplication is formal-series
convolution.

The norm is precisely Mathlib's weighted Gauss supremum. Restrictedness
implies that the weighted coefficients are bounded, so the conditionally
complete supremum has its asserted coefficient bounds. Strict positivity
of all radii gives zero detection. Mathlib's ultrametric estimates for
finite convolution sums prove submultiplicativity and the ultrametric
triangle inequality. They supply a normed commutative ring over any
ultrametric normed commutative coefficient ring.

A coefficient monomial has norm equal to the coefficient norm times its
weight. Constants preserve the coefficient norm, and norm one is inherited
when available. Over an ultrametric normed field the same construction is
a normed algebra. Trivial valuations, zero variables, incomplete
coefficients and, at ring level, the zero ring are permitted. The radius-one
algebra equivalence with `StrictTateAlgebra` preserves the actual coefficients
and the norms, hence is an isometry.

The finite-variable field construction is the normed-algebra portion of
Berkovich's Example 1.2.2(v), printed/PDF page 4, in *Non-Archimedean analytic
spaces*, Trieste lectures (2009). The relative series formula appears in
Definition 2.1.6(i), page 8. The original was read at pages 3-4 and 7-9.
Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`, retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.

The Lean construction allows an arbitrary variable type and ultrametric
normed commutative coefficient ring. This is an explicitly derived
extension of the source's finite-variable construction, with the cofinite
restrictedness convention and intrinsic norm laws proved here. For finitely
many variables, bounded total degree gives only finitely many exponents,
so the cofinite condition agrees with the source's total-degree escape
condition. No identification with another infinite-variable analytic
construction is asserted.

Completeness, polynomial density, general affinoid quotient presentations
and domain universal properties are subsequent obligations. This file
constructs the normed algebra and does not assert that it is already a
Banach algebra or a general affinoid algebra. It uses Mathlib's
`MvPowerSeries.IsRestricted.subring` and weighted Gauss estimates; no
rescaling by a field element of prescribed norm is assumed.
