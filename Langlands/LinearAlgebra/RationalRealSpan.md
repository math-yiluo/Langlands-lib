# Rational spans and kernels detected after real scalar extension

Author: Worker 1327.

This internal scalar-extension construction works for every additive
commutative group `M`, in every universe, without a torsion-free or finite-rank
assumption. `rationalRealEquiv` identifies
`ℝ ⊗[ℚ] (ℚ ⊗[ℤ] M)` with `ℝ ⊗[ℤ] M` using the standard tensor cancellation
equivalence. The rational-linear map `toReal` sends `q ⊗ m` to
`(q : ℝ) ⊗ m`. It is injective because extension of a rational vector space
to the real numbers preserves this inclusion.

Faithful scalar extension reflects membership of rational vectors in
subspaces: `1 ⊗ x` belongs to the real extension of `W` exactly when `x`
belongs to `W`. The proof applies faithful reflection of subspace inclusion
to the span of the singleton `x`. Extending the published `ratSpan R` and
transporting through `rationalRealEquiv` gives the real span of the vectors
`1 ⊗ m` for `m ∈ R`. Together these facts prove `toReal_mem_span_iff`.

Tensor induction shows that `toReal` commutes with scalar extension of every
integer-linear map `f : M → N`. Consequently, if the kernel of `f` after
real scalar extension equals that real span, the kernel after rational
scalar extension equals `ratSpan R`. One direction uses naturality and span
reflection; the other also uses injectivity of `toReal N`.

The provenance is internal tensor algebra. The module uses Mathlib's
associative scalar-extension equivalence, flatness over the field of
rational numbers, faithful flatness of its nonzero real vector space and
the universal property of a span. It makes no group-scheme structural
claim and assumes no character/root complement.
