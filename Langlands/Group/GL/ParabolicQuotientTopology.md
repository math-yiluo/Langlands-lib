# Topology of the actual GL parabolic quotient

Author: Worker 585.

This internal construction equips the existing multiplicative equivalence
`BlockShape.parabolicQuotientLevi` with continuity in both directions.
Its domain is the actual upper block-parabolic modulo the kernel of its
diagonal-block projection, with the quotient topology. Its codomain is the
existing product of the block general linear groups, with the product topology.
The coefficient ring is any commutative topological ring in an arbitrary
universe. No Hausdorff hypothesis or positive-rank hypothesis is needed.

`parabolicQuotientLeviContinuous` sends the class of `g` to its actual
diagonal-block projection. Its inverse sends `m` to the class of its
block-diagonal section. Forward continuity descends the continuous projection
through the quotient map. Inverse continuity composes the continuous section
with the quotient map.

`parabolicQuotientEmbeddedLeviContinuous` then composes with the existing
continuous equivalence from the product Levi to its block-diagonal image in GL.
The displayed formulas compute it on quotient representatives and compute its
inverse as the quotient class of the ambient Levi's inclusion in the parabolic.
The latter follows from the inverse law for the existing Levi equivalence.
Both constructions include rank zero and its empty product Levi.

The provenance is the explicit construction from the existing block projection,
section, subgroup and quotient. This module imports only the existing GL group
constructions and their Mathlib dependencies. It makes no assertion about a
general reductive datum, normalized functors, representation length, or Aubert
operators.
