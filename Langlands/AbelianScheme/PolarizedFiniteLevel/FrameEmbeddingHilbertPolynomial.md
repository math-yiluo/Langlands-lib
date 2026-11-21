# Hilbert-polynomial values of frame-normalized cubic embeddings

`cubicHilbertPolynomial g d` is the rational polynomial
`(6^g * d) * t^g`. The companion theorem computes the dimension used by
`HilbertSchemeUniversalFamilyStatement` for the image of an actual frame
embedding. The datum is over an affine scheme `Spec B`. The ideal `J` is
assumed to be the kernel of the frame embedding transported to the
fibre-product presentation of relative projective space. For every map
`B → K` to an algebraically closed field and every positive exponent `k`,
the geometric fibre dimension of sections of the `k`-th power of the
projective twist equals `cubicHilbertPolynomial g d` evaluated at `k`.

The proof first factors the transported closed immersion through
`J.subschemeι`. The resulting map is an isomorphism since the two closed
immersions have the same kernel. Its compatibility with the projection to
`Spec B` identifies the fibre of `J.subscheme` over `K` with the abelian
scheme of the base-changed datum. Compatibility with the other projection
identifies the pullback of the projective twist with the twist pulled back
by the base-changed frame embedding.

Over `K`, the frame-embedding isomorphism expresses that pulled-back twist
as the cubic bundle tensored with a line pulled back from `Spec K`. The field
line bundle is trivial; pullback of the unit and the tensor unitor remove
this factor. The proof then compares the iteration of `⊗` in the Hilbert
invariant to the explicit tensor power, commutes that power with pullback,
and applies `Datum.cubicPowerBundleIso`. The geometric `H⁰` rank is transported
along the fibre square and compared with degree-zero relative cohomology
using the global sections functor with its `K`-module structure. The
`Datum.cubicPowerFibreCohomology` formula now gives `(6*k)^g * d`, which equals
the evaluation of the polynomial.

This calculation is derived from the published frame-embedding and Hilbert
interfaces and the cubic-power cohomology calculation. It supplies the
polynomial in Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed.,
p. 131, used by the Hilbert-locus construction of Proposition 7.3. It does
not construct the locally closed frame locus or prove its finite type on
its own.
