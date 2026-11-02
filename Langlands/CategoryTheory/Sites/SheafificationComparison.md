# Comparing sheafifications for ordered topologies

This internal construction uses the universal property of Mathlib's
sheafification. Let `J ≤ K` be Grothendieck topologies on the same category,
and assume both admit weak sheafification with values in the given category.
Every `K`-sheaf is a `J`-sheaf. The unit for `K`-sheafification therefore
extends uniquely across `J`-sheafification, giving `comparison`.
`toSheafify_comparison` records its unit equation, and
`comparison_naturality` proves naturality in the original presheaf.

If the `J`-sheafification of a presheaf is itself a `K`-sheaf, its unit also
extends across `K`-sheafification. The two extensions are inverse by the
uniqueness part of sheafification. `comparisonIso` implements this argument
and records both unit equations. No exactness or concrete-category hypothesis
is used.

This is derived categorical infrastructure. In the Picard application the
ordered topologies are the big etale and fppf topologies on schemes over a
base. The required fppf sheaf property of the etale sheafification is an
explicit input here; this construction does not prove that property, stack
descent, or algebraic-space representability.
