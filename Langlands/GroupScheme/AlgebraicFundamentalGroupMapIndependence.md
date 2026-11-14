# Independence of geometric torus factorizations

This internal construction supports the induced map in Kaletha–Prasad, Lemma
11.3.6. It assumes the separately stated
`AlgebraicFundamentalGroupComparisonStatement`; it does not prove that statement.

The geometric chosen maximal tori remain maximal by field extension and split
over the separable closure by separably closed torus splitting. Two target tori
containing the same image are conjugate by a point centralizing that image.
Consequently their conjugation comparison respects both torus factorizations.
The assumed comparison formula on quotient representatives then identifies
their elementary quotient maps.

`factorizationMapTo` composes an elementary quotient map with canonical
comparison to any target presentation. The comparison composition law proves
that this map satisfies `IsInducedMap` for every geometric factorization.
Existence of a factorization over the original field therefore proves existence
of an induced map, conditional on the comparison statement.

All results here are derived from the Library constructions and comparison
statement; no additional external mathematical assertion is introduced.
