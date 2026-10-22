# Completed finite extensions and local norms

This construction builds the actual embedding of number-field
completions at a prime lying above another prime. The fields have independent
universes. Mathlib's comparison of normalized adic valuations supplies uniform
continuity of the original field embedding. Extending it by completion
constructs the local algebra and proves its compatibility with both original
field embeddings. Continuity of scalar multiplication is derived from
continuity of this ring homomorphism and multiplication.

Mathlib's finite-dimensionality theorem then applies to these constructed
algebra and scalar-tower instances. The local norm is the determinant norm
`Algebra.norm` of this actual finite extension. Its restriction to the base
completion is the extension-degree power, distinguishing it from the
completion embedding.

Continuity of the norm is proved by choosing a finite basis and expressing
it as the determinant of the matrix of multiplication. The map to that matrix
is linear, hence continuous on this finite-dimensional Hausdorff vector space
over its complete base field. The determinant is a polynomial and is
continuous. This argument uses the constructed continuous scalar action;
it does not assume that the normalized norms on two finite completions make
the field embedding isometric.

The local norm preserves the completed integral subring. The implemented
proof is topological: a continuous multiplicative map between nontrivially
normed fields that preserves zero carries the closed unit ball into the
closed unit ball. Given an element of norm at most one, all its powers
remain in that ball. Multiply those powers by one sufficiently small
nonzero element. Continuity at zero bounds all their images. If the image
of the original element had norm greater than one, its powers would
contradict that bound. The norm's multiplicativity guarantees that the
small nonzero element has nonzero image. Mathlib's equivalence between
normalized norm at most one and valuation at most one identifies these
balls with the genuine completed integral subrings.

`FiniteExtension.localUnitNorm` maps actual unit groups continuously using
the units topology. It also preserves the integral unit subgroup, since
the norm sends both an integral element and its integral inverse to
integral elements. These are proved properties, not assumptions.

At infinite places, `InfiniteExtension.localNorm` uses Mathlib's actual
completion algebra for places that lie over one another. Its finite
dimensionality is derived from the existing local-degree theorems (degree
one in the unramified case, two in the ramified case). The same determinant
argument proves continuity. The extension of the complex embedding proves
that the base completion is nontrivially normed. The continuous
`InfiniteExtension.localUnitNorm` is again the induced map on actual units.

The product over places above a place and compatibility with the global
field norm belong to the next construction group. No unproved
local/global compatibility is assumed here. This file alone does not
construct the adelic norm or descend it to idele classes.

Source: Andre Weil, *Basic Number Theory*, second edition (1973), Chapter III
section 1, definitions 2-4, printed pp. 43-45 (PDF pp. 60-62), for places and
completed extensions; Chapter III section 3, definition of the regular norm
and Proposition 4, printed p. 53 (PDF p. 70), for the determinant norm and
its behavior under a product decomposition; Chapter IV section 1, Corollary 3, printed p. 64 (PDF
p. 81), for the local product norm; Chapter IV section 3, the corollary on
printed p. 74 (PDF p. 91), for continuity of the idelic norm. The registered
source is `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
The completion-extension implementation is derived from Mathlib's uniform
completion interface. The original norm is the determinant of multiplication,
and the implemented continuity and integral-preservation arguments above are
construction proofs. Independent acceptance and publication are still required.
