# Stable Langlands data for an irreducible σ-stable representation

Use the Library's ordered tempered Langlands data over a \(p\)-adic
field. Entrywise pullback preserves the temperedness and irreducibility
of each factor and leaves the real determinant exponent unchanged as in
Henniart–Lemaire (2011), II.5.9. Section transport as in II.4.4
identifies the standard module of the pulled-back data with the
pullback of the original standard module. Covariance uses invariance
of the half modulus and of the determinant power characters.

`SigmaStableTemperedLanglandsHeadStatement` concerns irreducible admissible
σ-stable representations in positive rank. The field `F` has a specified
topology and is the base of the algebra automorphism `σ` of `E`. The supplied
topology on `E` is its `F`-module topology. If `E` is in `Type v`, the
input representation and its tempered blocks have carriers in
`Type (max v z)`.

Choose an irreducible Langlands head presentation using the Library's
strictly decreasing determinant exponents for upper normalized
induction. The pulled-back presentation has an isomorphic irreducible
head. Ordered-data uniqueness recovers the same block shape and
exponents and gives a block isomorphism at every index. Thus each
tempered block admits a twisting isomorphism, as in the stable
Langlands data step of the corollary in Henniart–Lemaire II.5.10.

For a characteristic-zero nonarchimedean local field, the corollary
uses `CharZeroLocalField.topologicalData` to apply the result with the
given topology. It uses the same `F`-module topology hypothesis and
carrier universe.
