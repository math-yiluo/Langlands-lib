# Relative finite-Galois point norms

This internal construction extends the existing coefficient norm to an intermediate
coefficient field, without changing the original group scheme or its point carriers.
Its intended consumer is the field-tower comparison in KP Lemma 2.5.12, which is
needed for the independence assertion of Lemma 2.6.24.

For a field tower `k → L → M`, `relativeExtend` is the actual coefficient map
`G(L) → G(M)`, and `relativeConjugate` uses restriction of an `L`-automorphism
of `M` to a `k`-automorphism. For an affine group scheme, relative fixed points
descend by applying the finite-Galois fixed-field theorem to each coordinate.
`relativeDescendCoordinates` is a `k`-algebra map to `L`; reconstructing the
point gives the multiplicative equivalence `relativeFixedEquiv`.

For an affine commutative group scheme, `relativeNorm` descends the product
over all `M/L` automorphisms. The theorem `relativeExtend_norm` verifies this
formula in the actual original point group. No splitting, valuation, norm
surjectivity, or independence conclusion is assumed or established by this
construction alone.

The construction and coordinate proof are derived from the published
`GaloisPointDescent` and `GaloisPointNorm` modules. The underlying norm is the
finite-Galois product norm used in Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Lemma 2.5.12 and Definition 2.5.13, printed pp.89–90
(PDF pp.120–121). The relative coordinate construction is internal
infrastructure rather than a separate assertion quoted from the book.
