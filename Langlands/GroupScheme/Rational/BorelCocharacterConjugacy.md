# Cocharacter conjugacy with respect to a field-defined Borel pair

`BorelCocharacterConjugacyStatement` concerns a geometric Borel subgroup
\(B\) of a connected reductive group \(G\), both defined over a field
\(k\), and a maximal \(k\)-torus \(T\) of \(G\) with a supplied
factorization of its inclusion through \(B\). Every \(k\)-cocharacter of
\(G\) is conjugate by a \(k\)-point of \(G\) to a cocharacter of \(T\)
whose dynamic parabolic contains \(B\) on every scheme test. Two
cocharacters of \(T\) with this containment that are conjugate by a
\(k\)-point are equal.

The proof `borelCocharacterConjugacy` chooses a cocharacter of \(T\)
presenting \(B\) with dynamic centralizer \(T\), using
`IsGeometricBorelSubgroup.exists_oppositeDynamicBorel`. A maximal split
torus through this cocharacter lies in \(T\). Its centralizer equals
that of the cocharacter, so this cocharacter is generic for the maximal
split torus. The rational chamber move
`exists_innerIso_comp_eq_dominant_cocharacter` then gives the conjugate
and the containment.

For uniqueness, the parabolic of the second cocharacter contains \(B\)
and the conjugate of \(B\) by the specified point. Thus this point lies in
that parabolic by `mem_rationalPoints_of_minimalParabolic_le_comap`.
Applying the limit homomorphism to the conjugacy over every test gives
conjugacy by a point of the second cocharacter's centralizer. The limit
homomorphism fixes the two cocharacters because both factor through \(T\).
Its value on the conjugating point centralizes the second cocharacter,
so the two cocharacters agree.
