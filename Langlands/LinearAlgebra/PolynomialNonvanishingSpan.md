# Linear spanning by polynomial nonvanishing

This internal linear-algebra module proves a density-to-spanning fact directly
from Mathlib's polynomial function extensionality. Let `b` be any finite basis
of a vector space `V` over an infinite field `k`, and let `p` be a nonzero
multivariate polynomial in its basis coordinates. The vectors `x` for which
`p(b.repr x)` is nonzero span `V`. The scalar, vector and basis-index universes
are independent. No positive-dimension assumption is made.

`basisLinearFormPolynomial b ℓ` is the sum of
`C (ℓ (b i)) * X i`. Evaluation at the coordinates of `x` equals `ℓ x`,
by the basis reconstruction identity and linearity. Consequently this
polynomial is zero exactly when `ℓ` is zero.

For `submodule_eq_top_of_polynomial_nonvanishing`, suppose a proper subspace
contains every vector at which `p` is nonzero. Mathlib's separating-functional
lemma provides a nonzero linear functional `ℓ` vanishing on that subspace.
The product of `p` and its linear-form polynomial evaluates to zero everywhere:
either the first factor vanishes, or the vector belongs to the subspace and
the second factor vanishes. `MvPolynomial.funext` over the infinite field
makes the product the zero polynomial. The polynomial ring is a domain,
contradicting the nonvanishing of both factors. Applying this result to the
linear span proves `span_polynomial_nonvanishing_eq_top`.
`exists_polynomial_nonvanishing` also records that the same nonvanishing
locus has a vector, using polynomial function extensionality and the
surjectivity of the basis coordinate map.

The provenance is this internal derivation from the imported Mathlib
polynomial and basis results. The intended application is the affine
Lie-space spanning step in the Cartan-generation proof. The module provides
no semisimple replacement, centralizer existence, or group-generation result.
