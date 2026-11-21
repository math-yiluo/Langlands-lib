# Common cuspidal support from restored identity coefficients

`HasRestoredCuspidalIdentityRealization` packages a single ordered tuple of
restored cuspidal realizations and a single irreducible target `Q`.
The finite induced subquotient of the normalized tuple is supplied as
its own witness. One full operator intertwiner onto `Q` is used at all
archimedean places. Its source has an identity evaluation in the tensor
of the restored realizations whose compact and finite translates separate
vectors. At each archimedean place the source satisfies the corresponding
compact and Lie module laws. Its identity coefficient has compact Levi
covariance and the unnormalized upper triangular Lie equation.

`hasProjectedCuspidalBlockRealization_of_restoredIdentity` applies the
same coefficient equivalence used for finite normalization. The
equivalence preserves separation and compact covariance and inserts the
outer half-modulus differential into the Lie equation. The identity
evaluation constructors then provide the real and complex place families
with the original quotient map.

This internal interface expresses which properties of the global projected
constant term are used in the place constituent argument. The construction
offers a common normalized tuple and quotient once those global properties
have been supplied.
