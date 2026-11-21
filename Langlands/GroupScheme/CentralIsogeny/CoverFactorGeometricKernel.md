# Comparison of finite covers by geometric kernels

`Langlands.GroupScheme.CoverFactorGeometricKernelStatement` concerns two
isogenies \(p \colon G \to Q\) and \(r \colon H \to Q\) over a
characteristic-zero field with \(Q\) affine and locally of finite type.
Given \(a \colon G \to H\) with \(r a = p\), suppose that the kernel map
lifts every kernel point on every algebraically closed coefficient field.
If the two geometric kernels have the same positive finite cardinality on
one such field, then \(a\) is an isomorphism.

For a point of \(H\), first lift its projection through \(p\). The difference
in \(H\) between this projected lift and the original point lies in the kernel
of \(r\). A lift of the difference corrects the first lift. Applied to all
algebraically closed coefficient fields, this gives surjectivity of the
underlying scheme map. The factor is finite since the composite and the
target isogeny are finite. Cartier reducedness of \(H\) and flatness of
dominant group homomorphisms then make the factor an isogeny. The geometric
kernel cardinality comparison identifies it as an isomorphism.

This derived comparison uses the actual scheme kernels and supplies the
cover comparison step needed for the spin stabilizer argument of Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), §§5.9–5.10,
pp. 93–95.
