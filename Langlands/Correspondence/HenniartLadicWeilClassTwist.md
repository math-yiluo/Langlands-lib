# Weil transport of ℓ-adic classes and unramified twists

`ladicWeilTwistParameter` is the injective group homomorphism sending
an unramified \(\ell\)-adic Galois character to its geometric Frobenius
value under the chosen complex coefficient embedding. Restricting a
twist to the local Weil group gives geometric degree powers of this
parameter. The identity intertwiner on the tensor product shows that
scalar extension commutes with these twists.
[Unramified ℓ-adic characters](HenniartLadicUnramifiedCharacters.md)

If two transported irreducible classes agree, their characters agree at
all projected Weil elements by the trace identity for scalar extension.
The original \(\ell\)-adic characters are continuous. Density of the
projection then gives equality of those characters on the absolute
Galois group. Character comparison identifies the original classes.

Conversely, suppose the transports of two rank-\(n>0\) classes differ
by a complex unramified twist with parameter \(z\). Comparing
determinants at geometric Frobenius shows that \(z^n\) is the image
of a ratio of \(\ell\)-adic determinants. These determinants are
continuous characters of the compact absolute Galois group, so the
ratio has norm one. Algebraic closedness places \(z\) in the image of
the coefficient embedding, and its \(\ell\)-adic preimage has norm one.
The unramified character with that Frobenius value gives the twist
between the original Galois classes by injectivity of transport.

The argument develops the twist comparison of \(\ell\)-adic and
complex classes in
`henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§§4.1–4.2, printed pp. 509–510 (PDF pp. 14–15).
