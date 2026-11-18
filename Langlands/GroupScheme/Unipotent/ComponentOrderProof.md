# The order of the geometric component group of a unipotent group

`Langlands.GroupScheme.unipotentComponentOrder.{u}` proves the published
[`UnipotentComponentOrderStatement`](ComponentOrderStatement.md), the order
assertion of Milne's Corollary 14.15. Let `H` be the base change of the given
unipotent affine algebraic group to `AlgebraicClosure k`. Affineness and
local finite type pass to `H` by pullback, and `IsUnipotent.baseChange`
supplies its unipotence.

- In characteristic zero, the characteristic exponent is `1`.
  `Unipotent.connectedSpace_of_isUnipotent_of_isAlgClosed` gives connectedness
  of `H`. Its component type is nonempty and subsingleton, so its cardinality
  is `1 = 1 ^ 0`.
- In prime characteristic `p`, `isPGroup_testPoints_of_isUnipotent` shows that
  `H(AlgebraicClosure k)` is a `p`-group. Its image under the surjective
  `componentPointProjection` is the finite group `ComponentPointQuotient H`,
  the quotient by the points in the identity component.
  `IsPGroup.iff_card` gives a power of `p` for its cardinality.
  `natCard_geometricComponents_eq_componentPointQuotient` identifies that
  cardinality with the number of geometric connected components of the
  original group. Local finite type over the algebraically closed field
  ensures every component of `H` contains a rational point.

Milne deduces the order assertion by applying Proposition 14.14 to the finite
étale component group in Proposition 2.37. The Lean proof uses the abstract
quotient of rational points over the algebraic closure in prime characteristic
and connectedness in characteristic zero. These arguments apply also to
nonsmooth groups.

J. S. Milne, *Algebraic Groups* (2017), Corollary 14.15 and Proposition 14.14
on printed p. 283 and Proposition 2.37 on printed p. 51.
Registered source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
