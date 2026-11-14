# A splitting extension normal over the local ground field

This internal helper strengthens the existing finite Galois splitting-field
construction in `KPZeroDatumConstruction` for the Galois-equivariance argument
of Task 6300. Its provenance is the published torus splitting theorem and
Mathlib's primitive element, normal compositum, and field-tower results.

For a nonarchimedean local field `F`, let `K = UnramifiedClosure F` and
`E = SeparableClosure F`. For every actual `F`-torus, `exists_normal_splitting`
constructs an intermediate field `L` of `E/K` that is finite Galois over `K`,
normal over `F`, and splits the torus. It gives no local-field structure to
`K` or `L`.

Choose an actual finite Galois splitting field `M/F` inside `E`, using
`exists_finiteGaloisSplittingField_inside`, and a primitive element `a` for
`M/F`. Set `L = K(a)`. Its underlying intermediate field over `F` is the
compositum of `K` and `M`, so it is normal over `F`. It is finite over `K`
because `a` is algebraic, and is Galois over `K` by tower normality and the
separability inherited from `E`. The inclusion `M → L` transports splitness
to `L` by the existing field-tower base-change theorem.
