# Covariant bilinear forms and their length

This internal algebraic adapter defines the actual submodule of bilinear forms
with simultaneous covariance `B(ρ(g)v, σ(g)w) = χ(g) B(v,w)`. It uses an arbitrary
field and monoid, with independent carrier universes. The function `χ` need
not satisfy a character law. The module length is valued in the extended
natural numbers, so no finite-dimensionality assumption is hidden.

Pullback along an intertwiner in the first argument preserves covariance.
It is injective for a surjective intertwiner and yields an actual linear
equivalence for an equivalence of representations. Swapping the two arguments
also yields an actual linear equivalence. The whole invariant subspace retains
the ambient length, and the zero subrepresentation has zero length.

`descendLeft` descends a form vanishing on a subrepresentation in its first
argument to the actual quotient. Its domain is the kernel of the actual
restriction map. Evaluation on quotient classes proves that this descent is
injective and preserves covariance.

`length_le_subrepresentation_add_quotient` writes the full form-space length
as the sum of the restriction kernel and its range. The range injects into the
form space on the subrepresentation, and quotient descent injects the kernel
into the form space on the quotient. Mathlib's length bounds for injections
give the claimed inequality.

The provenance is internal linear algebra over the existing actual
representation and subrepresentation constructions. No irreducible-pairing
classification or spectral-exception theorem is asserted.
