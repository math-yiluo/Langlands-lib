# Actual rational chart square for coefficient extension of a comparison

This is internal coherence for the existing coefficient-extension construction
on specified comparisons of actual formal atlases with full order action.
It is derived from that construction and the rational composition and inverse
laws; it asserts no new representability result.

For a specified comparison `c`, an `R`-algebra `S`, an `S`-algebra test `B`,
and a unit finer-cover generator, `baseChangeChartSquare` retains four actual
full-order rational maps. The top is evaluation of the rationalization of
`(c.baseChange S).coordinateIso`. The bottom is evaluation of the direct
coefficient extension `c.coordinateIso.baseChange S`. The left and right
vertical maps are the inverses of the evaluated `orderBaseChangeIso` maps for
the two refinements. The left generator is transported through the prescribed
equality of the two extended finer covers.

The commuting equation follows from the definition of `Comparison.baseChange`:
its coordinate isomorphism is the inverse left refinement correction, followed
by the extended original isomorphism and the right refinement correction.
The proof identifies the whole evaluated rational tensor with this composite
using compatibility of rationalization with formal composition, and cancels
the actual right correction with its inverse. It does not infer equality of
formal maps from their action on points.

All original atlases, order actions, covers, coefficient algebras and finite
coordinate types remain supplied. The coefficient map may merge generators;
the two original coordinate types and covers may differ, and the covers may
be infinite. The square is a supporting construction for reduction of framed
comparisons. Preservation of original framing squares under refinement and
composition remains a separate obligation.
