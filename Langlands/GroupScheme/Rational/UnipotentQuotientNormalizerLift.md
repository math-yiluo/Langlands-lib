# Exact normalizer lifts through smooth connected unipotent kernels

This is an internal supporting construction. It specializes the published
torus-conjugacy lift through split unipotent kernels to the normalizer of a
specified torus map.

At arbitrary universe `u`, let `k` be a field, `G` an affine group scheme over
`k`, and `r : N → G` a closed immersion with `N` smooth, connected and unipotent.
Let `q : G → Q` be an actual fppf quotient by the full subgroup functor represented
by `r`. Let `T` be a torus and `i : T → G` any homomorphism. Given an actual
`k`-point `n` of `Q` and a specified automorphism `σ` of `T` for which `n`
normalizes `i ≫ q` through `σ`, `splitNormalizerLift` constructs a point `m` of
`G` when `N` is split unipotent. Its subtype specification retains both exact
properties:

- `q(m) = n`;
- `m` normalizes `i` through this same automorphism `σ`.

Over a perfect field, `perfectFieldNormalizerLift` supplies the splitness from
smooth connected unipotence. The corresponding existence theorems give the
two properties together. `exists_normalizer_lift` allows a separately supplied
target torus map `i'` and an actual equality `i ≫ q = i'`.

The proof uses `fppfSplitUnipotentConjugator` in
`Rational.TorusUnipotentQuotientConjugacy` with both source torus maps equal to
`i` and with source isomorphism the underlying group isomorphism of `σ`.
The stable-vector and torus-action linearization hypotheses of that construction
are discharged by their published proofs. Its rational lift and kernel
correction preserve the specified quotient point, and its conjugacy equation is
exactly `IsNormalizingPoint i m σ`. Over a perfect field, the closed subgroup is
affine because `G` is affine, and `perfectFieldUnipotentSplit` supplies a finite
represented split unipotent series.

No injectivity, maximality or splitness of the torus map is needed. The
construction concerns rational points over a field. It does not assert an
integral lift over a local ring or a facet-root survival criterion.
