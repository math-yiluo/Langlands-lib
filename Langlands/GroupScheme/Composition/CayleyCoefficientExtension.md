# Coefficient extension of Cayley data

`Langlands.GroupScheme.CayleyDatum.extend` maps the coefficients of a Cayley datum over an infinite field of characteristic different from two to an extension field. The extended multiplication and unit are those used in the automorphism equations of `CayleyDatum`. The norm is the quadratic form of the coefficientwise image of its symmetric Gram matrix. `baseChangeNormIsometry` identifies this coordinate norm with tensor scalar extension of the original norm.

The unit identities are linear identities and extend by checking the standard basis. Multiplicativity of the norm is a polynomial identity in the coordinates of two vectors. The base field is infinite, so the identity on field-valued vectors holds for the polynomial of a pair of generic vectors. Evaluating it with extended coefficients proves multiplicativity after extension. The polar form is twice the Gram pairing, whose determinant stays nonzero under a field embedding.

This construction is derived from the structure-constant description in `CayleyDatum` and the Gram matrix scalar extension in `GramQuadraticComparison`.
