# The normalized σ-action on a generic unramified constituent

`Langlands.BaseChange.unramifiedGenericSigmaNormalization` proves
`Langlands.BaseChange.UnramifiedGenericSigmaNormalizationStatement.{uF,uE,uV}`.
It produces one σ-intertwining equivalence of the specified generic irreducible
subquotient. Its descent fixes every class in the actual Borel Jacquet quotient,
and the equivalence fixes every vector in the spherical fixed subspace. The two
field universes and the constituent's carrier universe are independent.

Choose a nontrivial additive character on the base field and pull it back by
the field trace. The resulting character is invariant under σ and gives the
same genericity predicate on the constituent by p-adic character independence.
Extend the constituent's Whittaker functional from its subquotient presentation
to the principal series using exactness of Whittaker functionals. This yields
an ambient coefficient model containing the constituent's coefficient model.

In the one-dimensional functional space of the principal series, composition
with the canonical pullback carries the extended functional to a nonzero
scalar multiple. The corresponding coefficient functions transform by that
scalar and precomposition, so the coefficient map's kernel is stable. The
canonical pullback descends to its quotient, the ambient coefficient model.
The range of the constituent's coefficient map is irreducible and contains
the least nonzero subrepresentation of the ambient model, so it equals that
subrepresentation. The descended intertwiner preserves this range in both
directions and restricts to the required equivalence on the constituent's
original carrier.

The canonical pullback fixes the principal series on its Jacquet quotient and
on its spherical vectors. For the Jacquet identity, coinvariants take the
coefficient quotient to a surjection and the constituent embedding to an
injection. For the spherical identity, compact open averaging lifts every
spherical vector of the coefficient quotient to a spherical vector of the
principal series. Both arguments use the same quotient and the same embedding
of the constituent. The input of cyclicity supplies finite order, and the
argument applies with the ramification-index equality in the published
statement. See the proofs in [BruhatJacquet](BruhatJacquet.md) and
[PrincipalSeries](PrincipalSeries.md).

The canonical operator and the passage through the Whittaker coefficient
quotient follow Henniart–Lemaire (2011), I.5.4, Lemma 1 and its proof, printed
p. 33 (PDF p. 41). The two identities are the Jacquet identity in the proof of
I.5.4, Lemma 2, printed p. 35 (PDF p. 43), and the spherical identity in the proof
of I.5.5, Lemma 2, printed p. 39 (PDF p. 47). The proof uses compact fixed-vector
exactness for the passage of the spherical identity to the generic constituent.
See the full citation and conventions in the
[normalized σ-action statement](../UnramifiedGenericSigmaNormalizationStatement.md).
