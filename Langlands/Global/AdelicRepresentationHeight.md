# Full adelic matrix-and-inverse heights

This module develops the normalized full local-product norm of an actual
matrix representation over a number field. At each place the local
maximum takes all entries of both the matrix and its inverse, as in the
doubled representation of Getz–Hahn (6.3). The infinite-place factors
carry the existing multiplicity `v.mult`, so complex norms are squared;
finite places use the actual normalized completion norms.

The exact formula is `sourceNorm`. It is defined on actual
adelic matrices, and `adelicSourceNorm` pulls it back through the given
group-scheme matrix representation. For positive matrix dimension the
finite-place maxima are at least one. The adele condition on the entries
of both the matrix and inverse makes them equal to one outside a finite
set. Thus the finite product is a genuine finite product.
`localMaximum_eq_norm_doubledMatrix` proves equality with the entry norm
of the actual block matrix consisting of the matrix and the transpose of
its inverse. This also accounts for the zero off-diagonal blocks.

The companion `height` multiplies each unnormalized infinite-place
maximum by the matrix dimension. It is a fixed scalar multiple of
`sourceNorm`, with scalar equal to the dimension raised to the sum of
infinite-place multiplicities. For positive dimension it is at least one,
invariant under inversion, and submultiplicative. The proof uses the
ordinary sum bound at infinite places and the ultrametric maximum bound
at finite places, together with the diagonal entry of the matrix-inverse
identity to obtain the lower bounds.
The same scalar identity and positive dimension prove strict positivity
of the unscaled source norm.

The general representation maps are the actual affine point maps and
existing general-linear multiplicative homeomorphism. Their full adelic
heights have these same identities. No faithfulness is needed for the
formulas or bounds. Identification as a proper norm and independence of
a chosen closed embedding require their own hypotheses and proofs.
For the standard representation of the explicit general-linear group
scheme, `adelicMatrix_standard` is exactly the existing actual matrix
homeomorphism, and both norm comparisons are literal equalities along
that map.

Source: Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), (6.3)–(6.4), printed p.158, and (6.7)–(6.8), printed p.161.
The finite-support argument uses the entries and their inverses directly.
It does not replace full adelic growth by the previously constructed
fixed-finite-slice archimedean growth predicate. Further growth-space and
original archimedean comparison results remain to be developed.
