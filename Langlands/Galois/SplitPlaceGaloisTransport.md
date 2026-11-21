# Reflection of Galois representation equivalence at a split place

Let a finite place \(v\) of a number field \(K\) split completely in an
extension \(E\), and let \(w\) be a place of \(E\) above \(v\).
`SplitPlaceGaloisTransportStatement` states that two finite-dimensional
representations of the absolute Galois group of \(K_v\) have an invertible
linear intertwiner exactly when their restrictions along the group map
induced by \(K_v\to E_w\) have one. The same coefficient field and carrier
spaces are used on both sides.

`absoluteGaloisMap_surjective_of_surjective` treats any surjective field
embedding. The larger field is integral over the smaller one, so its
chosen algebraic closure is also an algebraic closure of the smaller field.
An automorphism of the smaller field's algebraic closure lifts along the
chosen embedding. It fixes the larger base field because every element of
that field comes from the smaller one. Its restriction is the original
automorphism.

Complete splitting gives local degree one and therefore the actual
completion map is bijective. The induced map of absolute Galois groups is
surjective by the preceding lemma. `splitPlaceGaloisTransport` reuses
the same invertible linear map in both directions, using surjectivity to
test the intertwining relation on every element of the base Galois group.

This internal result uses the Library's actual completion map, definition
of complete splitting, and restriction of finite representations. It is
the split-place transport needed to use the quadratic base change in
Harris (1999), Theorem 5.9(ii), printed p. 315.
