# Constructing a normed algebraic closure above the Gauss point

Author: Worker 56.

For a nontrivially valued ultrametric field K, the earlier construction
of the Gauss point gives a multiplicative seminorm on the actual
finite-variable Tate algebra. This module uses the actual completed
residue field of that point: quotient by its kernel, fraction field,
induced absolute value, and metric completion. The existing residue-field
construction is due to Worker 36.
Completeness of K is unnecessary: the completion in the residue-field
construction supplies the complete field needed for norm extension.

The map from the Tate algebra into this completed residue field preserves
the Gauss norm, hence is injective. Its nontrivial norm follows from
that of K. The module then forms Mathlib's actual algebraic closure
of this complete field. Mathlib's norm-extension theorem equips it
with a multiplicative norm extending the complete field's norm.
The resulting field is algebraically closed and ultrametric; its
structure map from the Tate algebra is still exactly isometric.
Localization constructs its compatible scalar map from the fraction
field of the Tate algebra. The scalar-tower instances are proved.

These are concrete constructions from the Tate algebra and its Gauss
point. No normed extension, residue field, algebraic closure, or compatible
output map is taken as an additional hypothesis. This module supplies
the ambient valued field used to test roots in the spectral comparison;
it does not itself prove that roots of the affinoid minimal polynomial
have norm at most one.

The source motivation is the valued-extension step in the domain case
of Proposition 2.6.1, page 11, and Proposition 2.6.4, pages 11-12,
of the retained Berkovich-course notes. The formal route passes through
the completed Gauss residue field and uses Mathlib's
`spectralNorm.normedField` and `spectralNorm.normedAlgebra`, which
implement the norm-extension theorem for algebraic extensions of
complete nontrivially valued ultrametric fields.

Source: `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
retained PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
