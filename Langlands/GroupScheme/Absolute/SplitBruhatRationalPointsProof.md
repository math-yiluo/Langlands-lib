# Split Bruhat decomposition for the points of a Borel pair

`Langlands.GroupScheme.splitBruhatRationalPoints` proves
[`SplitBruhatRationalPointsStatement`](SplitBruhatRationalPointsStatement.md):
for a connected reductive group \(G\) over a field \(k\) and a Borel pair
\((B,T)\) with \(T\) split, the map \([n]\mapsto B(k)nB(k)\) from the Weyl
group `relativeWeylGroup t` to \(B(k)\backslash G(k)/B(k)\) is an
equivalence.

## Proof

Composites below are written in ordinary order: \(b\circ f\) means first
\(f\), then \(b\) (in Lean, `f ≫ b`).

The Borel pair supplies a factorization \(f : T\to B\) with
\(b\circ f = t\) (in Lean, `f ≫ b = t`). The third clause of
`regularCocharacterBorel` gives a cocharacter
\(\nu : \mathbb{G}_m\to T\) that is regular for \(t\) such that \(b\)
represents the dynamic parabolic \(P(t\circ\nu)\) of the cocharacter
\(t\circ\nu\) of \(G\); in particular the subgroup functor
`SubgroupFunctor.range b` equals
`Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t)`, which is
\(P(t\circ\nu)\).

A split maximal torus is a maximal split torus
(`IsMaximalTorus.isMaximalSplitTorus`). The relative roots
`relativeRoots t` are by definition the roots `roots t`, so a regular
cocharacter is generic (`IsGenericCocharacter`) for \(t\). Hence
`rationalBruhat` gives `HasRationalBruhatDecomposition t ν`, and
`hasRationalBruhatDecomposition_iff_bijective` turns it into bijectivity of
`relativeWeylToDoubleCosets t ν`, the map sending the class of a normalizer
point \(n\) to its double coset for the rational points of
\(P(t\circ\nu)\).

After unfolding `BorelTorusBruhatRationalPoints`, the representing
equality rewrites the rational points of \(B\) in the target into the
rational points of \(P(t\circ\nu)\). The equivalence is
`Equiv.ofBijective` of `relativeWeylToDoubleCosets t ν`, and its value on
the class of every normalizer point is the double coset of that point by
definition (`rfl`).

## Separably closed fields

`IsBorelPair.bruhatRationalPoints_of_isSepClosed` gives the same
conclusion for every Borel pair of a connected reductive group over a
separably closed field: there every torus is split by
`toriAreSplit_of_isSepClosed`, so `splitBruhatRationalPoints` applies.
