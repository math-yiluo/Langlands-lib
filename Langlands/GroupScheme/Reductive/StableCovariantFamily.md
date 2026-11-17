# Finite covariant families in translation-stable section spaces

This is derived supporting work for the independent affine homogeneous quotient
argument. It combines the finite regular covariance interface with rational
matrix detection of invariant split coordinates over an algebraically closed
field.

`familyLinearMap` takes ground-field linear combinations of a finite family of
actual global sections. Changing the family through a coordinate inclusion B
amounts to composing this linear map with multiplication by B.

`rightTranslation` is pullback along the actual right translation of the
ambient group by the image of a rational subgroup point. A covariant family's
linear combination transforms by its rational representation matrix. The proof
specializes the all-test covariance identity to the universal ambient point
and the constant subgroup point, then distributes the two finite sums.

If a ground-field subspace W of actual sections is stable under all these
rational translations, the inverse image of W under a covariant family's
linear map is invariant in any chosen split coordinates. Over an algebraically
closed field, for a reduced subgroup locally of finite type, rational matrix
stability implies stability on every relative scheme test. No reducedness
condition is placed on those tests.

`exists_covariantFamily_in_submodule` assumes additionally that the ambient
group is affine. For each s in W it supplies a natural number d, an actual
matrix representation of the subgroup on `Fin d`, sections f_j in W, and
coefficients v_j in k such that s is their linear combination and the family
is covariant on every relative scheme test.

The proof identifies s with its affine coordinate a, takes the finite regular
span of the singleton {a}, and chooses a finite basis. The existing actual
regular representation gives an all-test covariant family of global sections.
Take the inverse image U of W under its linear combination map, choose split
matrix coordinates for U, and apply the preceding stability criterion.
Restricting the regular family to those coordinates gives the required family
inside W. The original basis expansion of a and the split projection identity
show that its span contains s. No injectivity of the family map is assumed.

These are internal consequences of the published finite regular-span
construction, regular-basis transformation law, affine-coordinate comparison,
and rational detection of split-coordinate stability. They make no assertion
of geometric reductivity or of quotient affineness.
