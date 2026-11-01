# Compact actual corner averaging kernels

This internal prerequisite specializes the compact inverse corner Fourier family
to the Iwasawa parameters `(a,k)`. The right translate is
`h(a,k) = diag((product a)^(-1),a) k`. Its determinant equals `det k`, so it has
normalized determinant absolute value one for integral `k`.

The existing diagonal support bound supplies one compact clopen tail unit box,
independent of the nonzero determinant coordinate. Its product with the actual
integral subgroup is a compact clopen parameter set. The preceding joint-kernel
theorem yields a Schwartz function `K(a,k,v)` with joint compact support. For
every `g` in `GL_1` and integral `k`, its scalar plus Fourier integral, with the
unchanged supplied self-dual Haar measure, equals the actual unipotent transform
at `diag(det g / product a,a) k`. Outside the tail box, the existing diagonal
bound forces that transform to vanish, which justifies the cutoff uniformly in
`g`.

The derivation uses the published actual corner Fourier family, the original
Iwasawa coordinates and diagonal support bounds. It is a concrete compact
kernel construction. It does not yet push this kernel to a complex measure,
justify weighted integration against arbitrary model functions, or establish
the final paired matrix functional equation.
