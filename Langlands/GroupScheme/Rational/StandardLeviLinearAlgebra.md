# Linear algebra for standard Levi decompositions

Worker 624, internal derived helpers for the proof of the corrected Renard V.3.13
statement. These lemmas concern real vector spaces and do not introduce a new
source statement about group schemes.

The standard-Levi consumer uses the existing
`Langlands.LinearAlgebra.isCompl_orthogonal_of_positive` theorem and symmetry
of complements for its positive-form decomposition.

For a perfect real bilinear pairing `p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, `rightAnn` and
`leftAnn` are the inverse images of the usual dual annihilators under the two
maps of the pairing. The membership lemmas give their vanishing equations.
`rightAnn_leftAnn` and `leftAnn_rightAnn` prove double annihilation using
surjectivity onto the algebraic dual and Mathlib's double-annihilator theorem.
`rightAnn_isCompl` transports the dual-annihilator complement theorem through
the perfect-pairing equivalence.

`restricted_perfect` assumes finite dimension of `E` and complements of the
corresponding annihilators by subspaces `P` and `Q`. It proves that the pairing on
`leftAnn p Q × rightAnn p P` is perfect. Double annihilation places each kernel
vector in `P` or `Q`, respectively, and disjointness makes both kernels zero;
Mathlib's finite-dimensional criterion then gives perfectness.

`nested_complement` is the modular-lattice identity that restricts a complement
to a containing subspace. `projected_span` uses the projection onto a subspace
`A` along the span of the generators indexed by `J`. If `J ⊆ K`, the projection
kills the generators in `J` and sends the remaining generators into `A` with
difference in the smaller span. This proves that their projections span
`A ⊓ span (f '' K)`. Conversely each such projected generator belongs to this
intersection by subtraction. No independence assumption is needed.
