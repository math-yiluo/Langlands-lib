# A group structure on a supplied automorphism representer

This internal adapter constructs `GroupIsomorphismScheme.toGroupAutomorphismScheme`
from any supplied `GroupIsomorphismScheme G G`, over any scheme and in every
universe. It assumes representability and makes no existence or geometric
assertion. Its parameter scheme is definitionally the original parameter.

Natural local automorphisms form a group by composition:
`(e * f).toFun a g = e.toFun a (f.toFun a g)`. The identity is the identity
multiplicative equivalence on each test, and inversion uses the existing
`LocalGroupIso.symm`. Extensionality on every relative test proves the group
laws. Refinement preserves this structure, giving the group-valued
`LocalGroupIso.automorphismPresheaf`.

The supplied universal family represents the underlying set presheaf.
Mathlib's `GrpObj.ofRepresentableBy` therefore equips the same parameter
scheme with a group structure. `automorphismPointsEquiv` identifies its group
of points with natural local automorphisms, preserving composition in the
displayed order.

The actual evaluation morphism applies the universal family to the two
projections from the parameter times `G`. Naturality gives its evaluation
on every pair of points. The point-group equivalence proves the identity
and multiplication action laws, and each universal local automorphism
preserves multiplication in `G`. These laws define `evaluationAction`.
Its induced local family equals the original universal family on every
refinement. The original bijectivity then supplies exactly the
`GroupAutomorphismScheme` interface.

The construction and its proofs are derived from the published supplied-Isom,
natural-local-isomorphism, automorphic-action and supplied-Aut interfaces and
Mathlib's represented-group construction. No external mathematical result
or reductivity hypothesis is used.
