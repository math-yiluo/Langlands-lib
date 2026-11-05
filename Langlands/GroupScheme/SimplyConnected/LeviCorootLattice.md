# Saturation of spans of simple coroots

Author: Worker 1366.

This is a derived internal lattice argument for the proof of
`SplitTorusCentralizerDerivedSimplyConnectedStatement`. It makes no assertion
about a group scheme or the existence of a root-datum comparison.

`IsSaturatedIntSubmodule p` defines saturation for an integral submodule `p`:
for every nonzero integer `n` and every ambient vector `x`, membership of
`n • x` in `p` implies membership of `x` in `p`. This is a property of the
supplied submodule and makes no assertion that an arbitrary submodule has it.

`mem_span_basis_of_zsmul_mem` proves that the span of any subset of a basis of
an abelian group over the integers is saturated: if a nonzero integer multiple
of a vector lies in that span, the vector does too. The proof uses basis
coordinates. A coordinate of the vector can be nonzero only where the same
coordinate of its nonzero integer multiple is nonzero, since the integers
have no zero divisors.
`isSaturatedIntSubmodule_span_basis` packages this result using the defined
saturation predicate.

For a base `b` of an integral root pairing `P` with full coroot span,
`mem_span_simple_coroots_of_zsmul_mem` constructs a basis from the simple
coroots using their linear independence and `b.span_coroot_support`. Applying
the preceding result proves saturation for the span of any subset of the
simple coroots. Neither finiteness of all roots nor reducedness is needed.
`isSaturatedIntSubmodule_span_simple_coroots` records this saturation using
the same predicate.

`eq_top_of_finite_quotient_map_saturated` considers a submodule `p` of
finite index in an abelian group and an injective integral linear map `f`
whose image `p.map f` is saturated. Then `p` is the whole source group. For each source
element `y`, its class modulo `p` has finite additive order, so a positive
multiple of `y` belongs to `p`. Saturation places `f y` in `p.map f`,
and injectivity of `f` places `y` in `p`.

`eq_top_of_finite_quotient_map_eq_span_basis` applies this result when
`p.map f` is spanned by a subset of an integral basis.

`corootSpan_eq_top_of_map_eq_span_simple_coroots` applies the same argument
directly to the coroot spans of two supplied integral root pairings. Its
hypotheses include an ambient base with full coroot span, a subset of its
support, a finite quotient by the smaller coroot span, and an injective map
identifying the smaller coroot span with the span of that subset. Its
conclusion is that the smaller coroot span is the full smaller lattice.
All these comparison hypotheses remain explicit. The geometric construction
of these data for a centralizer and its derived subgroup is a separate
obligation.

The provenance is the elementary integral-basis argument described in the
paired Markdown of the public target statement, implemented here directly
using Mathlib's basis, root-base and finite-order APIs.
