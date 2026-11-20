# Closed-immersion reflection from supplied analytifications

Let `K` be a complete, nontrivially normed ultrametric field. Suppose `X'` and
`X` are separated algebraic spaces locally of finite type over `Spec K`, with
analytifications `(Y', p')` and `(Y, p)`. The theorem
`isClosedImmersion_of_closedImmersion` applies to a quasi-compact morphism
`f : X' ⟶ X` and a closed immersion `F : Y' ⟶ Y` compatible with the two
point families on every finitely presented affine test. It proves that `f`
is a closed immersion. The field, test algebras, and analytic spaces and
chart indices have the common universe `u`.

`CompactEtaleTest` stores an affine étale test with a compact subset of its
affine analytification. Given a compact subset `T` of `Y'` and the supplied
analytification of `X'`, `finiteCompactEtaleTestCover` chooses a finite set of
such tests whose images cover `T`. Each point lifts to an affine étale test
by joint surjectivity. A compact neighborhood of the lift gives an open
neighborhood of the point by étale openness. Compactness of `T` gives a
finite subcover from these open images.

Analytic closed immersions are monomorphisms and induce proper maps on
points. Reflection of monicity makes `f` a monomorphism, so its pullbacks
along affine étale tests of `X` are represented by schemes. Fix a test
`Spec A → X` and write its represented pullback as `W → Spec A`.
Quasi-compactness and local finite type allow the finite form of Zariski's
Main Theorem to factor this scheme monomorphism through an open subscheme
of a finite `Spec B → Spec A`.

The proof shows that the center preimage of the open image of `W` in the
affine analytification of `B` is closed. For a compact subset `L` of the
affine analytification of `A`, properness of `F` makes the inverse image
of the test image of `L` compact in `Y'`. Cover it using
`finiteCompactEtaleTestCover`. For each selected source test, separatedness
of `X` represents its overlap with `Spec A` by an algebra quotient of the
tensor product. Its joint analytic point map has compact inverse image
of the product of the chosen compact set in the source test and `L`.
The pullback property of `W` maps the overlap into `W` and hence into
`Spec B`, so the images of these compact sets lie over `L` in the required
center preimage.

Conversely, a point in that center preimage lying over `L` lifts along a
principal open contained in the image of `W`. Its image in `Y'` lies in
one of the chosen source tests. The two affine lifts have a compatible
point in their overlap by separatedness of `X'`, preservation of the
affine pullback by `p'`, and ordinary point lifting for analytic pullbacks.
The algebraic pullback maps this overlap to the one used above, producing
the original point of the affine analytification of `B`. Thus the slice
over `L` is a finite union of compact sets.

Compact neighborhoods in the affine analytification of `A` now show
closedness of the center preimage. The open image of `W` is constructible
by quasi-compactness, so affine constructible closedness detection shows it
is closed in `Spec B`. Its open immersion is then a closed immersion.
Consequently `W → Spec A` is finite and monic, hence a closed immersion.
The algebraic affine étale test criterion gives the result for `f`.

This uses Berkovich's properness and monomorphism argument for reflection
of closed immersions in *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), Proposition 3.4.7(2), printed p. 66. The
finite-cover construction and compact-slice proof are internal to the
Library's supplied affine test families. They obtain finiteness directly
on the represented affine tests.
