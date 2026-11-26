# Rational points of the normalizer of a Borel unipotent part

The theorem `Langlands.GroupScheme.borelUnipotentNormalizer.{u}` proves
[`BorelUnipotentNormalizerStatement.{u}`](BorelUnipotentNormalizerStatement.md).

Let `U` be the supplied unipotent part of the Borel subgroup `B`. The
multiplicative-type quotient of `B` makes `U` smooth and connected and
forces every unipotent subgroup of `B` to lie in `U`. The theorem on
unipotent parts of Borels then makes `U` a maximal smooth connected
unipotent subgroup of `G`.

The all-test normalizer of `U` has a closed representative `N`. Normality
of `U` in `B` gives the factorization of `B` through `N`. Since `B` is
smooth over the field, it factors through the reduction `P` of `N`.
The reduction is smooth, and the connectedness theorem for Borel
overgroups makes `P` connected. The subgroup `U` is still maximal
smooth connected unipotent in `P`. Pulling its ambient range back along
`P ⟶ G` gives its range in `P`, which is normal by the defining property
of `N`.

Take the affine fppf quotient of `P` by `U`. Its target is smooth by
descent and connected by surjectivity. A smooth connected unipotent
closed subgroup of the quotient has smooth connected inverse image
because the projection has smooth geometrically connected kernel. Its
inverse image is unipotent by the extension theorem. Maximality
identifies that inverse image with `U`, so the quotient subgroup has
trivial range. The torus criterion makes the quotient a torus, and the
extension theorem for solvable groups makes `P` solvable. Borel
maximality makes `B ⟶ P` an isomorphism.

Smoothness of `U` and density of rational points identify the abstract
normalizer of `U(k)` with the rational points of `N`. Every such point
lifts to `P` because the source `Spec k` is reduced, giving the equality
with the image of `B(k)`.

This is the reduced-normalizer argument in J. S. Milne, *Algebraic
Groups* (2017), Corollary 17.50, p. 368, using Theorem 16.33 and
Corollaries 17.25 and 17.49. The retained source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
